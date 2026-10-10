/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson
-/

module

public import LeanPool.ScottMeasurement.LinearInequalities.Definitions
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Rational vectors

Elementary closure facts used in Scott's reduction from relations to
inequalities on the rational difference set `Y - Y`.
-/

@[expose] public section

namespace Scott1964.MeasurementStructures.LinearInequalities

variable {S : Type*}

open scoped TensorProduct

theorem isRationalVector_zero : IsRationalVector (0 : S → ℝ) := by
  intro s
  exact ⟨0, by simp⟩

theorem IsRationalVector.neg {x : S → ℝ} (hx : IsRationalVector x) :
    IsRationalVector (-x) := by
  intro s
  obtain ⟨q, hq⟩ := hx s
  exact ⟨-q, by simp [hq]⟩

theorem IsRationalVector.sub {x y : S → ℝ}
    (hx : IsRationalVector x) (hy : IsRationalVector y) :
    IsRationalVector (x - y) := by
  intro s
  obtain ⟨q, hq⟩ := hx s
  obtain ⟨r, hr⟩ := hy s
  exact ⟨q - r, by simp [hq, hr]⟩

theorem rational_difference_set {Y : Set (S → ℝ)} (hY : IsRationalSet Y) :
    IsRationalSet {z | ∃ x ∈ Y, ∃ y ∈ Y, z = x - y} := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  exact (hY hx).sub (hY hy)

section PositiveKernel

variable {I : Type*} [Fintype I]
  [Finite S]

/-- A strictly positive real relation between finitely many rational vectors
can be replaced by a strictly positive rational relation.

This is the scalar-extension step in Scott's proof of Theorem 1.2.  Exactness
of tensoring the rational kernel with `ℝ` writes the given real relation as a
finite real linear combination of rational kernel vectors.  Density of a
finite product of copies of `ℚ` then preserves all strict coordinate
inequalities. -/
theorem exists_pos_rational_relation (x : I → S → ℝ)
    (hx : ∀ i, IsRationalVector (x i)) (c : I → ℝ)
    (hc : ∀ i, 0 < c i) (hsum : ∑ i, c i • x i = 0) :
    ∃ q : I → ℚ, (∀ i, 0 < q i) ∧ ∑ i, (q i : ℝ) • x i = 0 := by
  let := Fintype.ofFinite S
  classical
  choose a ha using fun i s ↦ hx i s
  let f : (I → ℚ) →ₗ[ℚ] (S → ℚ) :=
    { toFun := fun d s ↦ ∑ i, d i * a i s
      map_add' := by
        intro d e
        ext s
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro r d
        ext s
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum] }
  let eI := TensorProduct.piScalarRight ℚ ℝ ℝ I
  let eS := TensorProduct.piScalarRight ℚ ℝ ℝ S
  have hc_repr : eI.symm c = ∑ i, c i ⊗ₜ[ℚ] Pi.single i 1 := by
    apply eI.injective
    ext i
    simp [eI, Pi.single_apply]
  have hbase : f.baseChange ℝ (eI.symm c) = 0 := by
    rw [hc_repr]
    apply eS.injective
    ext s
    have hs := congrFun hsum s
    simpa [eS, f, Pi.single_apply, ha, Algebra.smul_def, smul_eq_mul, mul_comm] using hs
  have hexact :=
    Module.Flat.lTensor_exact ℝ (LinearMap.exact_subtype_ker_map f)
  rw [← LinearMap.baseChange_eq_ltensor] at hexact
  obtain ⟨t, ht⟩ := (hexact (eI.symm c)).mp hbase
  obtain ⟨k, r, v, rfl⟩ := TensorProduct.exists_sum_tmul_eq t
  let U : Set (Fin k → ℝ) :=
    {d | ∀ i, 0 < ∑ j, d j * ((v j : I → ℚ) i : ℝ)}
  have hrU : r ∈ U := by
    intro i
    have htc := congrArg eI ht
    have hi := congrFun htc i
    have hi' : ∑ j, r j * ((v j : I → ℚ) i : ℝ) = c i := by
      simpa [eI, Algebra.smul_def, smul_eq_mul, mul_comm] using hi
    rw [hi']
    exact hc i
  have hUopen : IsOpen U := by
    rw [show U = ⋂ i, {d | (0 : ℝ) < ∑ j, d j * ((v j : I → ℚ) i : ℝ)} by
      ext d
      simp [U]]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_lt continuous_const
    fun_prop
  have hdense : DenseRange (Pi.map fun _ : Fin k ↦ ((↑) : ℚ → ℝ)) :=
    DenseRange.piMap fun _ ↦ Rat.denseRange_cast
  obtain ⟨q, hqU⟩ := hdense.exists_mem_open hUopen ⟨r, hrU⟩
  let w : I → ℚ := fun i ↦ ∑ j, q j * (v j : I → ℚ) i
  refine ⟨w, ?_, ?_⟩
  · intro i
    have hi : (0 : ℝ) < ∑ j, (q j : ℝ) * ((v j : I → ℚ) i : ℝ) := by
      simpa using hqU i
    have hcast : (w i : ℝ) = ∑ j, (q j : ℝ) * ((v j : I → ℚ) i : ℝ) := by
      simp [w]
    rw [← hcast] at hi
    exact_mod_cast hi
  · have hv : ∀ j, f (v j : I → ℚ) = 0 :=
      fun j ↦ LinearMap.mem_ker.mp (v j).property
    ext s
    have hwzero : ∑ i, w i * a i s = 0 := by
      simp_rw [w, Finset.sum_mul]
      rw [Finset.sum_comm, Finset.sum_eq_zero]
      intro j hj
      have hfj := congrFun (hv j) s
      change (∑ i, (v j : I → ℚ) i * a i s) = 0 at hfj
      calc
        ∑ i, q j * (v j : I → ℚ) i * a i s =
            q j * ∑ i, (v j : I → ℚ) i * a i s := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = 0 := by rw [hfj, mul_zero]
    have hwzeroR := congrArg ((↑) : ℚ → ℝ) hwzero
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Rat.cast_sum, Rat.cast_mul, Rat.cast_zero, ha] using hwzeroR

end PositiveKernel

section Repetition

variable {L : Type*} [AddCommGroup L]

/-- Clearing to positive natural coefficients can be discharged by literal
repetition of each vector. -/
theorem UnweightedSequenceCancellation.natWeighted {X N : Set L}
    (h : UnweightedSequenceCancellation X N) :
    NatWeightedSequenceCancellation X N := by
  intro n x k hx hN hk hsum
  let I := Σ i : Fin (n + 1), Fin (k i)
  let i0 : I := ⟨0, ⟨0, hk 0⟩⟩
  have hI : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i0⟩
  let m := Fintype.card I - 1
  have hcard : Fintype.card I = m + 1 := by
    dsimp [m]
    omega
  let e : Fin (m + 1) ≃ I :=
    Fintype.equivOfCardEq (by simpa using hcard.symm)
  let z : Fin (m + 1) → L := fun j ↦ x (e j).1
  have hzsum : ∑ j, z j = 0 := by
    rw [← hsum]
    change ∑ j, x (e j).1 = ∑ i, k i • x i
    calc
      ∑ j, x (e j).1 = ∑ a : I, x a.1 := e.sum_comp (fun a ↦ x a.1)
      _ = ∑ i, ∑ _j : Fin (k i), x i := Fintype.sum_sigma (fun a : I ↦ x a.1)
      _ = ∑ i, k i • x i := by simp
  have hz := h m z (fun j ↦ hx (e j).1) (fun j ↦ hN (e j).1) hzsum
  intro i
  let a : I := ⟨i, ⟨0, hk i⟩⟩
  simpa [z, a] using hz (e.symm a)

end Repetition

section RationalRepetition

variable {S : Type*} [Finite S]

/-- On rational coordinate vectors, Scott's unit-weight cancellation
condition implies his arbitrary positive-real-weight condition. -/
theorem UnweightedSequenceCancellation.rationalWeighted
    {X N : Set (S → ℝ)} (h : UnweightedSequenceCancellation X N)
    (hX : IsRationalSet X) : WeightedSequenceCancellation X N := by
  let := Fintype.ofFinite S
  intro n x c hx hN hc hsum
  classical
  obtain ⟨q, hq, hqsum⟩ :=
    exists_pos_rational_relation x (fun i ↦ hX (hx i)) c hc hsum
  let D : ℕ := ∏ i, (q i).den
  have hden : ∀ i, (q i).den ∣ D := by
    intro i
    exact Finset.dvd_prod_of_mem (fun j ↦ (q j).den) (Finset.mem_univ i)
  choose d hd using hden
  let k : Fin (n + 1) → ℕ := fun i ↦ (q i).num.natAbs * d i
  have hnum : ∀ i, 0 < (q i).num := fun i ↦ Rat.num_pos.mpr (hq i)
  have hk : ∀ i, 0 < k i := by
    intro i
    have hD : 0 < D := Finset.prod_pos fun i _ ↦ (q i).den_pos
    have hdpos : 0 < d i := by
      have := hd i
      nlinarith [(q i).den_pos]
    exact Nat.mul_pos (Int.natAbs_pos.mpr (hnum i).ne') hdpos
  have hkq : ∀ i, (k i : ℚ) = (D : ℚ) * q i := by
    intro i
    have hnumcast : ((q i).num.natAbs : ℤ) = (q i).num :=
      Int.natAbs_of_nonneg (hnum i).le
    rw [← (q i).num_div_den]
    have hnumq : (0 : ℚ) < (q i).num := by exact_mod_cast hnum i
    norm_num [k, hd i, hnumcast, abs_of_pos hnumq]
    field_simp
  have hksum : ∑ i, k i • x i = 0 := by
    calc
      ∑ i, k i • x i = ∑ i, (k i : ℝ) • x i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (Nat.cast_smul_eq_nsmul ℝ (k i) (x i)).symm
      _ = ∑ i, ((D : ℚ) * q i : ℚ) • x i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← hkq i]
        rfl
      _ = (D : ℝ) • ∑ i, (q i : ℝ) • x i := by
        ext s
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp [Algebra.smul_def]
        ring
      _ = 0 := by rw [hqsum, smul_zero]
  exact h.natWeighted n x k hx hN hk hksum

end RationalRepetition

end Scott1964.MeasurementStructures.LinearInequalities
