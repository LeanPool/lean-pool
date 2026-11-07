/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Finite.Trace


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Trace fibers for the Kloosterman curve

Proves that the map `x ↦ x^p-x` has the prime field as kernel and the trace-zero
hyperplane as image. Each trace-zero fiber has exactly `p` points. Compare Harcos
(2015), equation (3).
-/

@[expose] public section

open scoped BigOperators

namespace KloostermanWeil.Stepanov

/-- The linear map `x ↦ x^p - x` on the degree-`n` finite field. -/
noncomputable def artinSchreierLinear (p n : ℕ) [Fact p.Prime] :
    GaloisField p n →ₗ[ZMod p] GaloisField p n :=
  (FiniteField.frobeniusAlgHom (ZMod p) (GaloisField p n)).toLinearMap -
    LinearMap.id

theorem artinSchreierLinear_apply (p n : ℕ) [Fact p.Prime]
    (x : GaloisField p n) : artinSchreierLinear p n x = x ^ p - x := by
  simp [artinSchreierLinear]

theorem artin_trace_zero (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (x : GaloisField p n) :
    Algebra.trace (ZMod p) (GaloisField p n) (x ^ p - x) = 0 := by
  apply (FaithfulSMul.algebraMap_injective (ZMod p) (GaloisField p n))
  rw [map_zero, FiniteField.algebraMap_trace_eq_sum_pow]
  rw [GaloisField.finrank p hn, Nat.card_zmod]
  have hterm (i : ℕ) :
      (x ^ p - x) ^ (p ^ i) =
        x ^ (p ^ (i + 1)) - x ^ (p ^ i) := by
    change iterateFrobenius (GaloisField p n) p i (x ^ p - x) = _
    rw [map_sub]
    simp only [iterateFrobenius_def]
    congr 1
    rw [← pow_mul]
    congr 1
    simp [pow_succ, mul_comm]
  have hxp : x ^ p ^ n = x := by
    have := Fintype.ofFinite (GaloisField p n)
    have hc : Fintype.card (GaloisField p n) = p ^ n := by
      rw [← Nat.card_eq_fintype_card]
      exact GaloisField.card p n hn
    rw [← hc]
    exact FiniteField.pow_card x
  simp_rw [hterm]
  calc
    (∑ i ∈ Finset.range n,
        (x ^ (p ^ (i + 1)) - x ^ (p ^ i))) =
        x ^ (p ^ n) - x ^ (p ^ 0) :=
      Finset.sum_range_sub (fun i => x ^ (p ^ i)) n
    _ = 0 := by rw [hxp]; simp

/-- The inclusion of the prime field into the kernel of `x ↦ x^p - x`. -/
noncomputable def artinKernelMap (p n : ℕ) [Fact p.Prime] :
    ZMod p →ₗ[ZMod p] (artinSchreierLinear p n).ker :=
  LinearMap.codRestrict (artinSchreierLinear p n).ker
    (Algebra.linearMap (ZMod p) (GaloisField p n)) (by
      intro r
      rw [LinearMap.mem_ker, artinSchreierLinear_apply,
        show (Algebra.linearMap (ZMod p) (GaloisField p n)) r =
          algebraMap (ZMod p) (GaloisField p n) r from rfl,
        ← (algebraMap (ZMod p) (GaloisField p n)).map_pow]
      simp)

theorem artinKernelMap_bijective (p n : ℕ) [Fact p.Prime] :
    Function.Bijective (artinKernelMap p n) := by
  constructor
  · intro a b hab
    apply FaithfulSMul.algebraMap_injective (ZMod p) (GaloisField p n)
    exact congrArg Subtype.val hab
  · intro x
    have hxpow : (x : GaloisField p n) ^ p = x := by
      have hx := x.property
      rw [LinearMap.mem_ker, artinSchreierLinear_apply, sub_eq_zero] at hx
      exact hx
    have hxbot : (x : GaloisField p n) ∈ (⊥ : Subfield (GaloisField p n)) :=
      (Subfield.mem_bot_iff_pow_eq_self (GaloisField p n) p).mpr hxpow
    obtain ⟨z, hz⟩ := (mem_bot_iff_intCast p (GaloisField p n)).mp hxbot
    refine ⟨(z : ZMod p), ?_⟩
    apply Subtype.ext
    change algebraMap (ZMod p) (GaloisField p n) (z : ZMod p) = x
    simpa using hz

/-- The prime field is linearly equivalent to the Artin–Schreier kernel. -/
noncomputable def artinKernelEquiv (p n : ℕ) [Fact p.Prime] :
    ZMod p ≃ₗ[ZMod p] (artinSchreierLinear p n).ker :=
  LinearEquiv.ofBijective (artinKernelMap p n)
    (artinKernelMap_bijective p n)

theorem finrank_artin_ker (p n : ℕ) [Fact p.Prime] :
    Module.finrank (ZMod p) (artinSchreierLinear p n).ker = 1 := by
  rw [← (artinKernelEquiv p n).finrank_eq]
  exact Module.finrank_self (ZMod p)

theorem artin_range_eq_trace_ker (p n : ℕ) [Fact p.Prime]
    (hn : n ≠ 0) :
    (artinSchreierLinear p n).range =
      (Algebra.trace (ZMod p) (GaloisField p n)).ker := by
  have hle : (artinSchreierLinear p n).range ≤
      (Algebra.trace (ZMod p) (GaloisField p n)).ker := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, artinSchreierLinear_apply]
    exact artin_trace_zero p n hn x
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hart := LinearMap.finrank_range_add_finrank_ker
    (artinSchreierLinear p n)
  rw [finrank_artin_ker, GaloisField.finrank p hn] at hart
  have htrange : (Algebra.trace (ZMod p) (GaloisField p n)).range = ⊤ :=
    LinearMap.range_eq_top.mpr
      (Algebra.trace_surjective (ZMod p) (GaloisField p n))
  have htr := LinearMap.finrank_range_add_finrank_ker
    (Algebra.trace (ZMod p) (GaloisField p n))
  rw [htrange, finrank_top, Module.finrank_self,
    GaloisField.finrank p hn] at htr
  omega

/-- The fiber of the Artin–Schreier linear map over `b`. -/
abbrev ArtinSchreierFiber (p n : ℕ) [Fact p.Prime]
    (b : GaloisField p n) :=
  {x : GaloisField p n // artinSchreierLinear p n x = b}

/-- Translation by a chosen preimage identifies a fiber with the kernel. -/
noncomputable def artinFiberEquivKernel (p n : ℕ) [Fact p.Prime]
    (b x₀ : GaloisField p n) (hx₀ : artinSchreierLinear p n x₀ = b) :
    (artinSchreierLinear p n).ker ≃ ArtinSchreierFiber p n b where
  toFun k := ⟨x₀ + k, by
    rw [map_add, hx₀, k.property, add_zero]⟩
  invFun y := ⟨y - x₀, by
    rw [LinearMap.mem_ker, map_sub, y.property, hx₀, sub_self]⟩
  left_inv k := by apply Subtype.ext; simp
  right_inv y := by apply Subtype.ext; simp

theorem card_artinSchreierFiber_of_trace_eq_zero
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (b : GaloisField p n)
    (hb : Algebra.trace (ZMod p) (GaloisField p n) b = 0) :
    Nat.card (ArtinSchreierFiber p n b) = p := by
  classical
  let := Fintype.ofFinite (GaloisField p n)
  rw [Nat.card_eq_fintype_card]
  have hmem : b ∈ (Algebra.trace (ZMod p) (GaloisField p n)).ker := by
    exact (LinearMap.mem_ker).mpr hb
  rw [← artin_range_eq_trace_ker p n hn] at hmem
  obtain ⟨x₀, hx₀⟩ := hmem
  calc
    Fintype.card (ArtinSchreierFiber p n b) =
      Fintype.card (artinSchreierLinear p n).ker :=
      Fintype.card_congr (artinFiberEquivKernel p n b x₀ hx₀).symm
    _ = Fintype.card (ZMod p) :=
      Fintype.card_congr (artinKernelEquiv p n).toEquiv.symm
    _ = p := ZMod.card p

end KloostermanWeil.Stepanov
