/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.FoldPipeline

/-!
# Validity of fold packs, and their existence by Nakayama lifting

The predicates on a fold pack (`ChabautyColeman.FoldCertData`) — its validity as a certificate pack
of the fold pipeline and its Weierstrass avoidance — and the existence of valid packs.

## Main definitions

* `ChabautyColeman.IsFoldCerts`: validity — the per-step Bézout identity of each triple
  against the pipeline state and the added point (no chain or degree conditions).
* `ChabautyColeman.IsFoldAvoid`: Weierstrass avoidance — coprime `(Uⱼ, 2·Vⱼ)` at every
  stage (the fold form of `ChabautyColeman.IsPipelineAvoid`).
* `ChabautyColeman.CanonShape`: the canonical pack shape — every step after the doubling
  step carries a pair certificate (`s₃ = 0`).

The predicates are parameterized by the configuration `(f, xs, ys, U₀, V₀)`, so the
*centre* versions need no separate definitions: the centre configuration is
`(foldXs x, foldYs y, tupleU x, tupleV x y)` at the witness tuple — exactly the data
`ChabautyColeman.exists_centerFoldWitness` delivers.

## Main statements

* `ChabautyColeman.IsFoldCerts.isFoldState`: valid packs give the stage invariants.
* `ChabautyColeman.IsFoldCerts.map`: the residue of a valid pack is valid.
* `ChabautyColeman.exists_isFoldCerts_lift`: over a base whose kernel lies in the Jacobson radical,
  a valid pack for the image configuration lifts with prescribed residues — one Bézout triple per
  step by Nakayama; no chain data needs lifting.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section Seq

variable {S S' : Type*} [CommRing S] [CommRing S'] {n : ℕ}

/-- The pack as a step sequence: junk triples beyond the fold's `2 * n` steps. -/
noncomputable def FoldCertData.seq (d : FoldCertData S n) : ℕ → FoldTriple S :=
  fun j ↦ if h : j < 2 * n then d ⟨j, h⟩ else ⟨0, 0, 0⟩

theorem FoldCertData.seq_of_lt (d : FoldCertData S n) {j : ℕ} (hj : j < 2 * n) :
    d.seq j = d ⟨j, hj⟩ := dite_eq_left hj

theorem FoldCertData.seq_map (φ : S →+* S') (d : FoldCertData S n) :
    (d.map φ).seq = fun j ↦ (d.seq j).map φ := by
  funext j
  rw [FoldCertData.seq, FoldCertData.seq]
  split_ifs
  · rfl
  · simp [FoldTriple.map]

end Seq

section Certs

variable {S : Type*} [CommRing S] {n : ℕ}

/-- **Validity of a fold pack** (replacing `IsFtauCerts`): the per-step Bézout identity
of each triple against the current pipeline state and the added point. Together with the
points lying on the curve this makes every pipeline state a fold state
(`ChabautyColeman.IsFoldCerts.isFoldState`) — no degree or chain conditions needed. -/
def IsFoldCerts (f : S[X]) (xs ys : ℕ → S) (U₀ V₀ : S[X]) (d : FoldCertData S n) : Prop :=
  ∀ j : Fin (2 * n),
    (d j).s₁ * (foldPipe f xs ys d.seq U₀ V₀ j).1 + (d j).s₂ * (X - C (xs j))
      + (d j).s₃ * ((foldPipe f xs ys d.seq U₀ V₀ j).2 + C (ys j)) = 1

/-- **Weierstrass avoidance of the fold pipeline** (the fold form of
`ChabautyColeman.IsPipelineAvoid`): at every stage — the start included — the state's
components are coprime, with the `2` of the half-differential included. -/
def IsFoldAvoid (f : S[X]) (xs ys : ℕ → S) (U₀ V₀ : S[X]) (d : FoldCertData S n) : Prop :=
  ∀ j ≤ 2 * n, IsCoprime (foldPipe f xs ys d.seq U₀ V₀ j).1
    (2 * (foldPipe f xs ys d.seq U₀ V₀ j).2)

/-- **The canonical shape of a fold pack**: every disjoint step (all steps after the
doubling step `0`) carries a pair certificate only — its third slot vanishes. -/
def CanonShape (d : FoldCertData S n) : Prop :=
  ∀ j : Fin (2 * n), 1 ≤ (j : ℕ) → (d j).s₃ = 0

variable {f : S[X]} {xs ys : ℕ → S} {U₀ V₀ : S[X]} {d : FoldCertData S n}

/-- Transport of a valid fold pack along an equality of index bounds. -/
theorem isFoldCerts_cast {n' : ℕ} (h : n' = n) (hd : IsFoldCerts f xs ys U₀ V₀ d) :
    IsFoldCerts (n := n') f xs ys U₀ V₀ (fun j ↦ d (Fin.cast (by rw [h]) j)) := by
  subst h
  exact hd

/-- Transport of fold-pipeline avoidance along an equality of index bounds. -/
theorem isFoldAvoid_cast {n' : ℕ} (h : n' = n) (hd : IsFoldAvoid f xs ys U₀ V₀ d) :
    IsFoldAvoid (n := n') f xs ys U₀ V₀ (fun j ↦ d (Fin.cast (by rw [h]) j)) := by
  subst h
  exact hd

/-- The per-step Bézout identities of a valid pack, in stage-indexed form. -/
theorem IsFoldCerts.bezout (hd : IsFoldCerts f xs ys U₀ V₀ d) {j : ℕ} (hj : j < 2 * n) :
    (d.seq j).s₁ * (foldPipe f xs ys d.seq U₀ V₀ j).1 + (d.seq j).s₂ * (X - C (xs j))
      + (d.seq j).s₃ * ((foldPipe f xs ys d.seq U₀ V₀ j).2 + C (ys j)) = 1 := by
  rw [d.seq_of_lt hj]
  exact hd ⟨j, hj⟩

/-- **The stage invariants from a valid pack**: every pipeline state of a valid fold pack at curve
points is a fold state. -/
theorem IsFoldCerts.isFoldState [Nontrivial S] (hf : f.Monic)
    (hfdeg : f.natDegree = 2 * n + 1) (h₀ : IsFoldState n f U₀ V₀)
    (hcv : ∀ j < 2 * n, ys j ^ 2 = f.eval (xs j)) (hd : IsFoldCerts f xs ys U₀ V₀ d)
    {m : ℕ} (hm : m ≤ 2 * n) :
    IsFoldState n f (foldPipe f xs ys d.seq U₀ V₀ m).1
      (foldPipe f xs ys d.seq U₀ V₀ m).2 :=
  isFoldState_foldPipe (m := m) hf hfdeg h₀ (fun j hj ↦ hd.bezout (by lia))
    fun j hj ↦ hcv j (by lia)

/-- **The residue of a valid pack is valid** at the image configuration. -/
theorem IsFoldCerts.map {S' : Type*} [CommRing S'] [Nontrivial S] (φ : S →+* S')
    (hf : f.Monic) (hfdeg : f.natDegree = 2 * n + 1) (h₀ : IsFoldState n f U₀ V₀)
    (hcv : ∀ j < 2 * n, ys j ^ 2 = f.eval (xs j)) (hd : IsFoldCerts f xs ys U₀ V₀ d) :
    IsFoldCerts (f.map φ) (fun j ↦ φ (xs j)) (fun j ↦ φ (ys j)) (U₀.map φ) (V₀.map φ)
      (d.map φ) := by
  intro j
  have hpipe := map_foldPipe (m := (j : ℕ)) φ hf hfdeg h₀
    (fun i hi ↦ hd.bezout (by lia)) fun i hi ↦ hcv i (by lia)
  have h1 : (foldPipe f xs ys d.seq U₀ V₀ j).1.map φ
      = (foldPipe (f.map φ) (fun i ↦ φ (xs i)) (fun i ↦ φ (ys i))
          (fun i ↦ (d.seq i).map φ) (U₀.map φ) (V₀.map φ) j).1 := congrArg Prod.fst hpipe
  have h2 : (foldPipe f xs ys d.seq U₀ V₀ j).2.map φ
      = (foldPipe (f.map φ) (fun i ↦ φ (xs i)) (fun i ↦ φ (ys i))
          (fun i ↦ (d.seq i).map φ) (U₀.map φ) (V₀.map φ) j).2 := congrArg Prod.snd hpipe
  have hbez := congrArg (Polynomial.map φ) (hd j)
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one,
    Polynomial.map_sub, Polynomial.map_X, map_C, h1, h2] at hbez
  rwa [FoldCertData.seq_map]

end Certs

/-! ### Existence of valid packs by Nakayama lifting -/

section Exists

variable {R A : Type*} [CommRing R] [Nontrivial R] [CommRing A] {φ : R →+* A} {n : ℕ}
  {f : R[X]} {xs ys : ℕ → R} {U₀ V₀ : R[X]}

/-- One step of the pack lifting: extend a partially lifted pack by the Nakayama lift of
the next Bézout identity. -/
private theorem exists_lift_step (hsurj : Function.Surjective φ)
    (hker : RingHom.ker φ ≤ Ideal.jacobson ⊥) (hf : f.Monic)
    (hfdeg : f.natDegree = 2 * n + 1) (h₀ : IsFoldState n f U₀ V₀)
    (hcv : ∀ j < 2 * n, ys j ^ 2 = f.eval (xs j)) {d' : FoldCertData A n}
    (hd' : IsFoldCerts (f.map φ) (fun j ↦ φ (xs j)) (fun j ↦ φ (ys j)) (U₀.map φ)
      (V₀.map φ) d') {m : ℕ} (hm : m < 2 * n) {e : ℕ → FoldTriple R}
    (hbez : ∀ j < m, (e j).s₁ * (foldPipe f xs ys e U₀ V₀ j).1
      + (e j).s₂ * (X - C (xs j))
      + (e j).s₃ * ((foldPipe f xs ys e U₀ V₀ j).2 + C (ys j)) = 1)
    (hres : ∀ j < m, (e j).map φ = d'.seq j) :
    ∃ e' : ℕ → FoldTriple R,
      (∀ j < m + 1, (e' j).s₁ * (foldPipe f xs ys e' U₀ V₀ j).1
        + (e' j).s₂ * (X - C (xs j))
        + (e' j).s₃ * ((foldPipe f xs ys e' U₀ V₀ j).2 + C (ys j)) = 1)
      ∧ ∀ j < m + 1, (e' j).map φ = d'.seq j := by
  classical
  -- the upstairs state at stage `m` and its residue identification
  have hstate := isFoldState_foldPipe (m := m) hf hfdeg h₀ hbez fun j hj ↦ hcv j (by lia)
  have hpipe := map_foldPipe (m := m) φ hf hfdeg h₀ hbez fun j hj ↦ hcv j (by lia)
  have h1a : (foldPipe f xs ys e U₀ V₀ m).1.map φ
      = (foldPipe (f.map φ) (fun i ↦ φ (xs i)) (fun i ↦ φ (ys i))
          (fun i ↦ (e i).map φ) (U₀.map φ) (V₀.map φ) m).1 := congrArg Prod.fst hpipe
  have h2a : (foldPipe f xs ys e U₀ V₀ m).2.map φ
      = (foldPipe (f.map φ) (fun i ↦ φ (xs i)) (fun i ↦ φ (ys i))
          (fun i ↦ (e i).map φ) (U₀.map φ) (V₀.map φ) m).2 := congrArg Prod.snd hpipe
  have hcongr := foldPipe_congr (f := f.map φ) (xs := fun i ↦ φ (xs i))
    (xs' := fun i ↦ φ (xs i)) (ys := fun i ↦ φ (ys i)) (ys' := fun i ↦ φ (ys i))
    (U₀ := U₀.map φ) (V₀ := V₀.map φ) (m := m) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hres
  have h1 := h1a.trans (congrArg Prod.fst hcongr)
  have h2 := h2a.trans (congrArg Prod.snd hcongr)
  -- lift the downstairs Bézout identity of step `m`
  have habc := hd'.bezout (j := m) hm
  rw [← h1, ← h2] at habc
  have habc' : (d'.seq m).s₁ * (foldPipe f xs ys e U₀ V₀ m).1.map φ
      + (d'.seq m).s₂ * ((X - C (xs m)).map φ)
      + (d'.seq m).s₃ * (((foldPipe f xs ys e U₀ V₀ m).2 + C (ys m)).map φ) = 1 := by
    rwa [Polynomial.map_sub, Polynomial.map_X, map_C, Polynomial.map_add, map_C]
  obtain ⟨s₁, s₂, s₃, hs, hs₁, hs₂, hs₃⟩ :=
    exists_bezout_lift_map hsurj hker hstate.monicU habc'
  refine ⟨Function.update e m ⟨s₁, s₂, s₃⟩, ?_, ?_⟩
  · intro j hj
    have hagree : ∀ i < j, Function.update e m ⟨s₁, s₂, s₃⟩ i = e i := fun i hi ↦
      Function.update_of_ne (by lia) ..
    rw [foldPipe_congr (fun i hi ↦ rfl) (fun i hi ↦ rfl) hagree]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
    · rw [Function.update_of_ne (by lia)]
      exact hbez j hj'
    · rw [Function.update_self]
      exact hs
  · intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
    · rw [Function.update_of_ne (by lia)]
      exact hres j hj'
    · rw [Function.update_self]
      simp only [FoldTriple.map, hs₁, hs₂, hs₃]

/-- **Existence of a valid fold pack over a Jacobson-covered base**: a valid pack for the image
configuration lifts, one Bézout triple per step by Nakayama
(`ChabautyColeman.exists_bezout_lift_map`), to a valid pack with prescribed residues. No chain or
degree data needs lifting — the fold is chain-free. -/
theorem exists_isFoldCerts_lift (hsurj : Function.Surjective φ)
    (hker : RingHom.ker φ ≤ Ideal.jacobson ⊥) (hf : f.Monic)
    (hfdeg : f.natDegree = 2 * n + 1) (h₀ : IsFoldState n f U₀ V₀)
    (hcv : ∀ j < 2 * n, ys j ^ 2 = f.eval (xs j)) (d' : FoldCertData A n)
    (hd' : IsFoldCerts (f.map φ) (fun j ↦ φ (xs j)) (fun j ↦ φ (ys j)) (U₀.map φ)
      (V₀.map φ) d') :
    ∃ d : FoldCertData R n, IsFoldCerts f xs ys U₀ V₀ d ∧ d.map φ = d' := by
  -- build the pack one step at a time, with prescribed residues
  have main : ∀ m ≤ 2 * n, ∃ e : ℕ → FoldTriple R,
      (∀ j < m, (e j).s₁ * (foldPipe f xs ys e U₀ V₀ j).1 + (e j).s₂ * (X - C (xs j))
        + (e j).s₃ * ((foldPipe f xs ys e U₀ V₀ j).2 + C (ys j)) = 1)
      ∧ ∀ j < m, (e j).map φ = d'.seq j := by
    intro m hm
    induction m with
    | zero => exact ⟨fun _ ↦ ⟨0, 0, 0⟩, fun j hj ↦ absurd hj (by lia), fun j hj ↦
        absurd hj (by lia)⟩
    | succ m ih =>
      obtain ⟨e, hbez, hres⟩ := ih (by lia)
      exact exists_lift_step hsurj hker hf hfdeg h₀ hcv hd' (by lia) hbez hres
  obtain ⟨e, hbez, hres⟩ := main (2 * n) le_rfl
  refine ⟨fun j ↦ e j, fun j ↦ ?_, ?_⟩
  · have hagree : ∀ i < (j : ℕ), FoldCertData.seq (n := n) (fun j ↦ e j) i = e i :=
      fun i hi ↦ FoldCertData.seq_of_lt _ (by lia)
    rw [foldPipe_congr (fun i hi ↦ rfl) (fun i hi ↦ rfl) hagree]
    exact hbez j j.isLt
  · funext j
    have h := hres j j.isLt
    rwa [d'.seq_of_lt j.isLt] at h

end Exists

end ChabautyColeman

end
