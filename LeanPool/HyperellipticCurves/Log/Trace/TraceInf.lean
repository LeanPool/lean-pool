/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Trace.TracePipeline

/-!
# The two-block Cantor addition and its trace identity

The configuration of the infinity chart has only **two** blocks — the moving point (a
degree-one Mumford datum with constant `v`-part) and the `τ`-block — composed once and
reduced once: stages 1–2 of the generic Cantor pipeline
(`ChabautyColeman.cantorStage₂`), with no auxiliary point and no constant pair block. This
file supplies what that addition needs; the configuration itself and its trace-form identity
live in `LeanPool.HyperellipticCurves.Log.Trace.TraceKzInf`.

## Main statements

* `ChabautyColeman.IsAddCerts`: validity of a certificate pack for the two-block addition
  (the later fields of the pack are unused), together with the reduced-datum invariants
  `ChabautyColeman.cantorStage₂_monic_dvd_degree_lt`;
* `ChabautyColeman.traceDiff_cantorStage₂`: (T1) + (T2) along the two-block addition.

Blueprint node: `thm:omega-prime-global`, clause (c), infinity chart.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

/-! ### The two-block Cantor addition -/

section AddCerts

variable {R : Type*} [CommRing R] (f : R[X]) (D : PipelineData R) (dt : CantorCertData R)

/-- Validity of a certificate pack for the two-block Cantor addition `D₁ + D₂` — stages 1–2
of the generic pipeline; the later fields of the pack are unused: the composition Bézout
certificate holds, the reduction certificate inverts the cofactor's leading coefficient, and
the final `u`-part has degree `n`. -/
structure IsAddCerts (n : ℕ) : Prop where
  /-- The Bézout certificate of the composition step. -/
  hbez : dt.s₁ * D.u₁ + dt.s₂ * D.u₂ + dt.s₃ * (D.v₁ + D.v₂) = 1
  /-- The inverse of the leading coefficient of the cofactor, normalizing the reduction. -/
  hc : dt.c₁ * (cantorCofactor f (cantorStage₁ f D dt).1 (cantorStage₁ f D dt).2).leadingCoeff = 1
  /-- The reduced support has the prescribed degree. -/
  hdeg : (cantorStage₂ f D dt).1.natDegree = n

variable {f D dt} {n : ℕ}

/-- The two-block addition returns a reduced Mumford datum. -/
theorem cantorStage₂_monic_dvd_degree_lt [Nontrivial R] (hu₁ : D.u₁.Monic)
    (hd₁ : D.u₁ ∣ D.v₁ ^ 2 - f) (hu₂ : D.u₂.Monic) (hd₂ : D.u₂ ∣ D.v₂ ^ 2 - f)
    (hcerts : IsAddCerts f D dt n) :
    (cantorStage₂ f D dt).1.Monic
      ∧ (cantorStage₂ f D dt).1 ∣ (cantorStage₂ f D dt).2 ^ 2 - f
      ∧ (cantorStage₂ f D dt).2.degree
        < (cantorStage₂ f D dt).1.degree := by
  have hS₁m : (cantorStage₁ f D dt).1.Monic := cantorCompose_monic f hu₁ hu₂
  have hS₁d : (cantorStage₁ f D dt).1 ∣ (cantorStage₁ f D dt).2 ^ 2 - f :=
    cantorCompose_dvd f hcerts.hbez hd₁ hd₂
  exact ⟨cantorReduce_monic f hcerts.hc, cantorReduce_dvd f hS₁m hS₁d hcerts.hc,
    cantorReduce_degree_lt f hcerts.hc⟩

/-- **The one-step certificate pack for adding a point to a block**: over a curve of odd
degree `2n + 1`, adding a point `(α, y)` to a reduced block of degree `n` whose support is
coprime to `X - α` is certified by `⟨s₁, s₂, 0, -1, 1, 0, 0, 0⟩`, and the reduced output has
degree `n` again — the cofactor of the composed datum is monic up to the sign `-1`. -/
theorem isAddCerts_ofPair [Nontrivial R] [NoZeroDivisors R] {u₂ v₂ s₁ s₂ : R[X]} {α y : R}
    (hf : f.Monic) (hfdeg : f.natDegree = 2 * n + 1) (hy : y ^ 2 = f.eval α)
    (hu₂ : u₂.Monic) (hdeg₂ : u₂.natDegree = n) (hd₂ : u₂ ∣ v₂ ^ 2 - f)
    (hbez : s₁ * (X - C α) + s₂ * u₂ = 1) :
    IsAddCerts f (.ofPair (X - C α) (C y) u₂ v₂) ⟨s₁, s₂, 0, -1, 1, 0, 0, 0⟩ n := by
  have hu₁ : (X - C α : R[X]).Monic := monic_X_sub_C α
  have hd₁ : (X - C α : R[X]) ∣ C y ^ 2 - f := by
    rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_pow, eval_C, hy]
    ring
  have hbez₁ : s₁ * (X - C α) + s₂ * u₂ + 0 * (C y + v₂) = 1 := by linear_combination hbez
  have hS₁deg : ((X - C α) * u₂ : R[X]).natDegree = n + 1 := by
    rw [hu₁.natDegree_mul hu₂, hdeg₂, natDegree_X_sub_C, add_comm]
  set S₁ := cantorCompose f (X - C α) (C y) u₂ v₂ s₁ s₂ 0
  obtain ⟨hlcW, hWdeg⟩ := leadingCoeff_natDegree_cantorCofactor f hf hfdeg
    (cantorCompose_monic f hu₁ hu₂) hS₁deg (cantorCompose_dvd f hbez₁ hd₁ hd₂)
    (cantorCompose_degree_lt f hu₁ hu₂) (by lia)
  have hc : (-1 : R) * (cantorCofactor f S₁.1 S₁.2).leadingCoeff = 1 := by rw [hlcW]; ring
  have hdeg : (cantorReduce f S₁.1 S₁.2 (-1)).1.natDegree = n := by
    change (C (-1 : R) * cantorCofactor f S₁.1 S₁.2).natDegree = n
    rw [natDegree_C_mul (neg_ne_zero.mpr one_ne_zero)]
    lia
  exact ⟨hbez₁, hc, hdeg⟩

end AddCerts

section AddTrace

variable {S R : Type*} [CommRing S] [CommRing R] [Algebra S R] [Nontrivial R]
  [NoZeroDivisors R] (d : Derivation S R R)
  {f c₁ c₂ cP s₁ s₂ sP : R[X]} {D : PipelineData R} {dt : CantorCertData R}
  {n g k : ℕ}

/-- **The trace-form differential is additive along the two-block Cantor addition**: the
value on the reduced output of `D₁ + D₂` is the sum of the values on the two blocks. -/
theorem traceDiff_cantorStage₂ (hu₁ : D.u₁.Monic) (hd₁ : D.u₁ ∣ D.v₁ ^ 2 - f) (hu₂ : D.u₂.Monic)
    (hd₂ : D.u₂ ∣ D.v₂ ^ 2 - f) (hcerts : IsAddCerts f D dt n)
    (hfc : ∀ i, d (f.coeff i) = 0) (hf : f.natDegree = 2 * g + 1) (hk : k < g)
    (hs₁ : c₁ * D.u₁ + s₁ * (2 * D.v₁) = 1) (hs₂ : c₂ * D.u₂ + s₂ * (2 * D.v₂) = 1)
    (hsP : cP * (cantorStage₂ f D dt).1 + sP * (2 * (cantorStage₂ f D dt).2) = 1) :
    traceDiff d (cantorStage₂ f D dt).1 sP k
      = traceDiff d D.u₁ s₁ k + traceDiff d D.u₂ s₂ k := by
  have hS₁m : (cantorStage₁ f D dt).1.Monic := cantorCompose_monic f hu₁ hu₂
  have hS₁d : (cantorStage₁ f D dt).1 ∣ (cantorStage₁ f D dt).2 ^ 2 - f :=
    cantorCompose_dvd f hcerts.hbez hd₁ hd₂
  obtain ⟨cS₁, sS₁, hsS₁⟩ : IsCoprime (cantorStage₁ f D dt).1
      (2 * (cantorStage₁ f D dt).2) :=
    isCoprime_cantorCompose hcerts.hbez hd₁ hd₂ ⟨c₁, s₁, hs₁⟩ ⟨c₂, s₂, hs₂⟩
  rw [cantorStage₂_def] at hsP
  rw [cantorStage₂_def, traceDiff_cantorReduce d hS₁m hS₁d hcerts.hc hfc hf hk hsS₁ hsP]
  exact traceDiff_cantorCompose d hu₁ hu₂ hcerts.hbez hd₁ hd₂ hs₁ hs₂ hsS₁ k

end AddTrace

end ChabautyColeman

end
