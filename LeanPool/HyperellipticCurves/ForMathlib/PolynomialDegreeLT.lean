/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Polynomial.DegreeLT

import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Localization.Integral

/-!
# Dimension of spaces of polynomials of bounded degree

Four facts about a subspace `V` of the polynomials over a field, three of them about spaces
of bounded degree, together with the general statement about saturated lattices over a local
ring that the last one rests on.

## Main statements

* `IsLocalRing.linearIndependent_map_of_saturated`: the reductions of a basis of a submodule
  saturated with respect to an element `π` of the maximal ideal are linearly independent
  over the residue field.
* `Polynomial.finrank_add_natDegree_le_of_forall_dvd`: if a fixed `q` divides every element
  of a nonzero `V`, then `dim V + deg q ≤ n` — multiplication by `q` embeds the polynomials
  of degree `< n - deg q` onto a space containing `V`. Vanishing at `r` prescribed points is
  the case `q = ∏ (X - xᵢ)`, so it cuts the dimension down by `r`.
* `Polynomial.exists_forall_natDegree_le_of_ne_bot`: a nonzero `V` all of whose elements
  have degree `< n` contains an element of maximal degree.
* `Polynomial.exists_dvd_forall_mem_and_rootMultiplicity_le`: the minimal root multiplicities
  of a nonzero `V` at the points of a finite set `S` assemble into a nonzero polynomial
  dividing every element of `V` whose multiplicity at each of those points is attained in `V`.
* `Polynomial.exists_submodule_map_residue`: **reduction of a lattice preserves dimension**.
  For a subspace `W` over the fraction field `L` of a discrete valuation ring `O`, the
  polynomials over the residue field that lift to *integral* polynomials in `W` contain a
  subspace of dimension at least `dim_L W`. The lattice `W ∩ O[X]_n` is free over the
  principal ideal domain `O`, and it is saturated (`π⁻¹ · h` is again integral and in `W`),
  which is what makes the reductions of one of its bases linearly independent.
-/

@[expose] public section

open Module

namespace IsLocalRing

variable {O : Type*} [CommRing O] [IsLocalRing O] {M : Type*} [AddCommGroup M] [Module O M]
  {M' : Type*} [AddCommGroup M'] [Module O M'] [Module (ResidueField O) M']
  [IsScalarTower O (ResidueField O) M']

/-- **The reductions of a basis of a saturated submodule are linearly independent.** Here
`N` is a submodule of `M` saturated with respect to an element `π` of the maximal ideal
(`π • w ∈ N → w ∈ N`), and `f` is a linear map into a module over the residue field whose
kernel consists of multiples of `π`. A combination of the basis `bb` of `N` whose image
under `f` vanishes is `π` times an element of `M`, hence — by saturation — `π` times an
element of `N`, so all its coordinates are divisible by `π` and their residues vanish. -/
theorem linearIndependent_map_of_saturated {ι : Type*} [Finite ι] {N : Submodule O M} {π : O}
    (hπ : π ∈ maximalIdeal O) (bb : Basis ι O N) (hsat : ∀ w : M, π • w ∈ N → w ∈ N)
    (f : M →ₗ[O] M') (hker : ∀ v : M, f v = 0 → ∃ w : M, v = π • w) :
    LinearIndependent (ResidueField O) fun i ↦ f (bb i : M) := by
  have := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  choose c' hc' using fun i ↦ residue_surjective (R := O) (c i)
  set v : N := ∑ i, c' i • bb i with hv
  have hvcoe : (v : M) = ∑ i, c' i • (bb i : M) := by rw [hv]; simp
  have hv0 : f (v : M) = 0 := by
    rw [hvcoe, map_sum, ← hc]
    exact Finset.sum_congr rfl fun j _ ↦ by
      rw [map_smul, ← hc' j, ← ResidueField.algebraMap_eq, algebraMap_smul]
  obtain ⟨w, hw⟩ := hker _ hv0
  have hwN : w ∈ N := hsat w (by rw [← hw]; exact v.2)
  have hvw : v = π • (⟨w, hwN⟩ : N) := Subtype.ext (by rw [hw]; rfl)
  have hrepr : ⇑(bb.repr v) = c' := by rw [hv]; exact bb.repr_sum_self c'
  have hci : c' i = π * bb.repr ⟨w, hwN⟩ i := by rw [← congrFun hrepr i, hvw, map_smul]; simp
  rw [← hc' i, hci, map_mul, (residue_eq_zero_iff _).mpr hπ, zero_mul]

end IsLocalRing

namespace Polynomial

/-- **A nonzero subspace `V` of polynomials of degree `< n` all of whose elements are
divisible by `q` satisfies `dim V + deg q ≤ n`**: multiplication by `q` maps the polynomials
of degree `< n - deg q` onto a space containing `V`. Nonzeroness of `V` is what makes `q`
nonzero and its degree smaller than `n`. -/
theorem finrank_add_natDegree_le_of_forall_dvd {κ : Type*} [Field κ] {V : Submodule κ κ[X]}
    {q : κ[X]} (hV : V ≠ ⊥) (hdvd : ∀ h ∈ V, q ∣ h) {n : ℕ} (hdeg : ∀ h ∈ V, h.degree < n) :
    finrank κ V + q.natDegree ≤ n := by
  obtain ⟨h₀, hh₀V, hh₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
  have hq : q ≠ 0 := fun h ↦ hh₀ (zero_dvd_iff.mp (h ▸ hdvd h₀ hh₀V))
  have hle : V ≤ Submodule.map (LinearMap.mulLeft κ q) κ[X]_(n - q.natDegree) := by
    intro h hh
    obtain ⟨s, rfl⟩ := hdvd h hh
    refine ⟨s, ?_, rfl⟩
    simp only [SetLike.mem_coe, mem_degreeLT]
    rcases eq_or_ne s 0 with rfl | hs
    · simp
    · rw [← natDegree_lt_iff_degree_lt hs]
      have h4 : (q * s).natDegree < n :=
        (natDegree_lt_iff_degree_lt (mul_ne_zero hq hs)).mpr (hdeg _ hh)
      rw [natDegree_mul hq hs] at h4
      lia
  have key : finrank κ V ≤ n - q.natDegree :=
    (Submodule.finrank_mono hle).trans ((Submodule.finrank_map_le _ _).trans
      (le_of_eq ((finrank_eq_card_basis (degreeLT.basis κ _)).trans (by simp))))
  lia [(natDegree_lt_iff_degree_lt hq).mpr <|
    (degree_le_of_dvd (hdvd h₀ hh₀V) hh₀).trans_lt (hdeg h₀ hh₀V)]

section

variable {κ : Type*} [Field κ] {V : Submodule κ κ[X]}

/-- **A nonzero space of polynomials of bounded degree has an element of maximal degree**:
the degrees of the nonzero elements of `V` are bounded above by `n`, so the largest of them
is attained. -/
theorem exists_forall_natDegree_le_of_ne_bot {n : ℕ} (hV : V ≠ ⊥) (hdeg : ∀ h ∈ V, h.degree < n) :
    ∃ h ∈ V, h ≠ 0 ∧ ∀ h' ∈ V, h'.natDegree ≤ h.natDegree := by
  obtain ⟨h₀, hh₀V, hh₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
  have hbdd : BddAbove {k | ∃ h ∈ V, h ≠ 0 ∧ h.natDegree = k} := by
    refine ⟨n, ?_⟩
    intro k ⟨h, hhV, hh0, hk⟩
    exact hk ▸ ((natDegree_lt_iff_degree_lt hh0).mpr (hdeg h hhV)).le
  obtain ⟨h, hhV, hh0, hh⟩ := Nat.sSup_mem (s := {k | ∃ h ∈ V, h ≠ 0 ∧ h.natDegree = k})
    ⟨h₀.natDegree, h₀, hh₀V, hh₀, rfl⟩ hbdd
  refine ⟨h, hhV, hh0, fun h' hh'V ↦ ?_⟩
  rcases eq_or_ne h' 0 with rfl | h'0
  · simp
  · exact hh ▸ le_csSup hbdd ⟨h', hh'V, h'0, rfl⟩

/-- The polynomial assembled from the minimal root multiplicities of `V` at the points of a
finite set `S`: it divides every element of `V`, and at each `x ∈ S` its multiplicity is
already attained by an element of `V`. -/
theorem exists_dvd_forall_mem_and_rootMultiplicity_le (hV : V ≠ ⊥) (S : Finset κ) :
    ∃ q ≠ 0, (∀ h ∈ V, q ∣ h) ∧
      ∀ x ∈ S, ∃ h ∈ V, h ≠ 0 ∧ rootMultiplicity x h ≤ rootMultiplicity x q := by
  classical
  obtain ⟨h₀, hh₀V, hh₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
  set μ : κ → ℕ := fun x ↦ sInf {k | ∃ h ∈ V, h ≠ 0 ∧ rootMultiplicity x h = k}
  have hq0 : (∏ x ∈ S, (X - C x) ^ μ x) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun x _ ↦ pow_ne_zero _ (X_sub_C_ne_zero x)
  have hμmem (x : κ) : ∃ h ∈ V, h ≠ 0 ∧ rootMultiplicity x h = μ x :=
    Nat.sInf_mem (s := {k | ∃ h ∈ V, h ≠ 0 ∧ rootMultiplicity x h = k}) ⟨_, h₀, hh₀V, hh₀, rfl⟩
  have hμle {x : κ} {h : κ[X]} (hhV : h ∈ V) (hh0 : h ≠ 0) : μ x ≤ rootMultiplicity x h :=
    Nat.sInf_le (s := {k | ∃ h ∈ V, h ≠ 0 ∧ rootMultiplicity x h = k}) ⟨h, hhV, hh0, rfl⟩
  refine ⟨_, hq0, fun h hhV ↦ ?_, fun x hx ↦ ?_⟩
  · rcases eq_or_ne h 0 with rfl | hh0
    · exact dvd_zero _
    · refine Finset.prod_dvd_of_coprime (fun i _ j _ hij ↦ ?_)
        fun i _ ↦ (le_rootMultiplicity_iff hh0).mp (hμle hhV hh0)
      exact (pairwise_coprime_X_sub_C Function.injective_id hij).pow
  · obtain ⟨h, hhV, hh0, hmult⟩ := hμmem x
    exact ⟨h, hhV, hh0,
      hmult.le.trans ((le_rootMultiplicity_iff hq0).mpr (Finset.dvd_prod_of_mem _ hx))⟩

end

variable {O : Type*} [CommRing O] [IsDomain O]
  {L : Type*} [Field L] [Algebra O L] [IsFractionRing O L]

/-- Mapping a linear combination with coefficients in the base ring. -/
private theorem map_sum_smul {R S ι : Type*} [Semiring R] [Semiring S] (s : Finset ι)
    (φ : R →+* S) (c : ι → R) (b : ι → R[X]) :
    (∑ i ∈ s, c i • b i).map φ = ∑ i ∈ s, φ (c i) • (b i).map φ := by
  simp [Polynomial.map_sum, Polynomial.map_smul]

/-- **The lattice of integral polynomials of degree `< n` lying in `W` is saturated**: if
`π * w` is in it, so is `w`. -/
private theorem mem_of_C_mul_mem {n : ℕ} {W : Submodule L L[X]} {N : Submodule O O[X]} {π : O}
    (hπ : π ≠ 0) (hmemN : ∀ h : O[X], h ∈ N ↔ h.degree < n ∧ h.map (algebraMap O L) ∈ W)
    {w : O[X]} (hw : C π * w ∈ N) : w ∈ N := by
  obtain ⟨hdv, hmv⟩ := (hmemN _).mp hw
  have hπL : algebraMap O L π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O L)).mpr hπ
  refine (hmemN w).mpr ⟨?_, ?_⟩
  · rcases eq_or_ne w 0 with rfl | hwne
    · simp
    · rwa [degree_mul, degree_C hπ, zero_add] at hdv
  · have heq : (algebraMap O L π)⁻¹ • (C π * w).map (algebraMap O L) = w.map (algebraMap O L) := by
      rw [Polynomial.map_mul, map_C, smul_eq_C_mul, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hπL,
        C_1, one_mul]
    rw [← heq]
    exact Submodule.smul_mem _ _ hmv

variable [IsDiscreteValuationRing O]

open IsLocalRing in
/-- **The reductions of a basis of a saturated lattice are linearly independent.** The
specialization of `IsLocalRing.linearIndependent_map_of_saturated` to `M = O[X]` and the
reduction map: a polynomial whose reduction vanishes has all its coefficients in the
maximal ideal, hence is divisible by the uniformizer `π`. -/
private theorem linearIndependent_map_residue {m : ℕ} {N : Submodule O O[X]} {π : O}
    (hπ : Irreducible π) (bb : Basis (Fin m) O N) (hsat : ∀ w : O[X], C π * w ∈ N → w ∈ N) :
    LinearIndependent (ResidueField O) fun i ↦ (bb i : O[X]).map (residue O) := by
  have hπm : maximalIdeal O = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have := linearIndependent_map_of_saturated (M' := (ResidueField O)[X])
    (hπm ▸ Ideal.mem_span_singleton_self π) bb
    (fun w hw ↦ hsat w (by rwa [smul_eq_C_mul] at hw)) (mapAlg O (ResidueField O)).toLinearMap
    (fun v hv ↦ ?_)
  · simpa [mapAlg_eq_map, ResidueField.algebraMap_eq] using this
  · rw [AlgHom.toLinearMap_apply, mapAlg_eq_map, ResidueField.algebraMap_eq] at hv
    obtain ⟨w, hw⟩ : C π ∣ v := (C_dvd_iff_dvd_coeff _ _).mpr fun k ↦ by
      have h0 : residue O (v.coeff k) = 0 := by rw [← coeff_map, hv, coeff_zero]
      rwa [residue_eq_zero_iff, hπm, Ideal.mem_span_singleton] at h0
    exact ⟨w, by rw [hw, smul_eq_C_mul]⟩

/-- **A lattice of integral polynomials spans the subspace it comes from**: clearing
denominators moves any element of `W` into the lattice, so `W` lies in the span of the
images of a basis. -/
private theorem le_span_map_of_basis {n m : ℕ} {W : Submodule L L[X]} {N : Submodule O O[X]}
    (hW : ∀ h ∈ W, h.degree < n) (bb : Basis (Fin m) O N)
    (hmemN : ∀ h : O[X], h ∈ N ↔ h.degree < n ∧ h.map (algebraMap O L) ∈ W) :
    W ≤ Submodule.span L (Set.range fun i ↦ (bb i : O[X]).map (algebraMap O L)) := by
  set φ := algebraMap O L
  intro x hx
  obtain ⟨a, ha, hax⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors O) x
  set p := IsLocalization.integerNormalization (nonZeroDivisors O) x
  have ha0 : φ a ≠ 0 :=
    (map_ne_zero_iff φ (IsFractionRing.injective O L)).mpr (nonZeroDivisors.ne_zero ha)
  have hax' : p.map φ = φ a • x := by rw [hax, algebraMap_smul]
  have hdeg : p.degree < n := by
    rw [← degree_map_eq_of_injective (IsFractionRing.injective O L), hax', smul_eq_C_mul,
      degree_mul, degree_C ha0, zero_add]
    exact hW x hx
  have hpN : p ∈ N := (hmemN p).mpr ⟨hdeg, hax' ▸ Submodule.smul_mem _ _ hx⟩
  have hcoe : p = ∑ i, bb.repr ⟨p, hpN⟩ i • (bb i : O[X]) := by
    have h1 : ((∑ i, bb.repr ⟨p, hpN⟩ i • bb i : N) : O[X])
        = ∑ i, bb.repr ⟨p, hpN⟩ i • (bb i : O[X]) := by push_cast; rfl
    rwa [bb.sum_repr] at h1
  have hx' : x = (φ a)⁻¹ • ∑ i, φ (bb.repr ⟨p, hpN⟩ i) • (bb i : O[X]).map φ := by
    rw [← map_sum_smul, ← hcoe, hax', smul_smul, inv_mul_cancel₀ ha0, one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ ↦
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

open IsLocalRing in
variable (O) in
/-- **Reduction of a lattice preserves dimension**: for a subspace `W` of the polynomials
of degree `< n` over the fraction field, the reductions of the *integral* polynomials in
`W` span a subspace of the polynomials over the residue field of dimension at least
`dim W`, and every element of that subspace lifts to an integral polynomial in `W`.

The lattice `W ∩ O[X]_n` is free over the principal ideal domain `O`; it is saturated
(`Polynomial.mem_of_C_mul_mem`), so the reductions of a basis of it stay linearly
independent (`Polynomial.linearIndependent_map_residue`), and it spans `W` over the
fraction field (`Polynomial.le_span_map_of_basis`). -/
theorem exists_submodule_map_residue {n : ℕ} (W : Submodule L L[X])
    (hW : ∀ h ∈ W, h.degree < n) :
    ∃ V : Submodule (ResidueField O) (ResidueField O)[X],
      finrank L W ≤ finrank (ResidueField O) V ∧
      ∀ h ∈ V, ∃ h₀ : O[X], h₀.map (residue O) = h ∧ h₀.map (algebraMap O L) ∈ W := by
  classical
  set φ := algebraMap O L
  set N : Submodule O O[X] :=
    O[X]_n ⊓ Submodule.comap (mapAlg O L).toLinearMap (W.restrictScalars O) with hNdef
  have hmemN (h : O[X]) : h ∈ N ↔ h.degree < n ∧ h.map φ ∈ W := by
    rw [hNdef, Submodule.mem_inf, mem_degreeLT, Submodule.mem_comap]
    rfl
  obtain ⟨m, bb⟩ := Submodule.basisOfPidOfLE (N := N) inf_le_left (degreeLT.basis O n)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hind := linearIndependent_map_residue hπ bb fun _ hw ↦ mem_of_C_mul_mem hπ.ne_zero hmemN hw
  refine ⟨Submodule.span (ResidueField O) (Set.range fun i ↦ (bb i : O[X]).map (residue O)),
    ?_, fun h hh ↦ ?_⟩
  · have hfin : Module.Finite L (Submodule.span L (Set.range fun i ↦ (bb i : O[X]).map φ)) :=
      Module.Finite.span_of_finite L (Set.finite_range _)
    rw [finrank_span_eq_card hind, Fintype.card_fin]
    exact (Submodule.finrank_mono (le_span_map_of_basis hW bb hmemN)).trans
      (by simpa [Set.finrank] using finrank_range_le_card (R := L) fun i ↦ (bb i : O[X]).map φ)
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hh
    choose c' hc' using fun i ↦ residue_surjective (R := O) (c i)
    refine ⟨∑ i, c' i • (bb i : O[X]), ?_, ?_⟩
    · rw [map_sum_smul, ← hc]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [hc']
    · rw [map_sum_smul]
      exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ ((hmemN _).mp (bb j).2).2

end Polynomial

end
