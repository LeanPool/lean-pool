/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Carlitz.FactorWeight
public import LeanPool.KloostermanWeil.Carlitz.IrreducibleGhost
public import Mathlib.Data.Multiset.Replicate


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Indexing Newton sums

Finite indexing and coefficient identities for the Newton-sum recurrence associated
with Carlitz (1969).
-/

@[expose] public section

namespace KloostermanWeil.Carlitz

open Polynomial
open KloostermanWeil.Dickson

theorem prod_heq_of_heq
    {α α' β β' : Type}
    {a : α} {a' : α'} {b : β} {b' : β'}
    (ha : a ≍ a') (hb : b ≍ b') :
    (a,b) ≍ (a',b') := by
  cases ha
  cases hb
  rfl

theorem nested_sigma_heq
    {α : Type}
    {γ : α → Type}
    {δ : (a : α) → γ a → Type}
    {a a' : α} (ha : a = a')
    {q : γ a} {q' : γ a'}
    (hq : q ≍ q')
    {k : δ a q} {k' : δ a' q'}
    (hk : k ≍ k') :
    (Sigma.mk q k : Σ z : γ a, δ a z) ≍
      (Sigma.mk q' k' : Σ z : γ a', δ a' z) := by
  subst a'
  have hqe : q = q' := eq_of_heq hq
  subst q'
  have hke : k = k' := eq_of_heq hk
  subst k'
  rfl

noncomputable instance factorDataFintype
    (p n : ℕ) [Fact p.Prime] :
    Fintype (FactorData p n) :=
  Fintype.ofEquiv (Fin n → ZMod p) (coeffFactorEquiv p n)

noncomputable instance relevantIrredFintype
    (p n : ℕ) [Fact p.Prime] [NeZero n] :
    Fintype (RelevantIrred p n) := by
  letI : Finite (ConjRootClass (Fp p) (Ext p n)) := by
    unfold ConjRootClass
    infer_instance
  letI := Fintype.ofFinite (ConjRootClass (Fp p) (Ext p n))
  exact Fintype.ofEquiv
    (ConjRootClass (Fp p) (Ext p n))
    (classRelevantEquiv p n)

abbrev PointedFactorData
    (p n : ℕ) [Fact p.Prime] :=
  Σ s : FactorData p n,
    Σ q : {q : Polynomial (ZMod p) // q ∈ s.1.toFinset},
      Fin (s.1.count q.1)

abbrev PrimePowerDecomp
    (p n : ℕ) [Fact p.Prime] :=
  Σ j : Fin n,
    RelevantIrred p (j.1 + 1) ×
      FactorData p (n - (j.1 + 1))

noncomputable def primePowerToPointed
    (p n : ℕ) [Fact p.Prime] :
    PrimePowerDecomp p n → PointedFactorData p n := by
  rintro ⟨j, P, u⟩
  let d := P.1.natDegree
  have hdpos : 0 < d := P.2.2.1.natDegree_pos
  have hdvd : d ∣ j.1 + 1 := P.2.2.2
  let r := (j.1 + 1) / d
  have hrpos : 0 < r := by
    apply Nat.div_pos
    · exact Nat.le_of_dvd (by omega) hdvd
    · exact hdpos
  have hrne : r ≠ 0 := Nat.ne_of_gt hrpos
  have hrd : r * d = j.1 + 1 := by
    dsimp [r]
    exact Nat.div_mul_cancel hdvd
  let sm : Multiset (Polynomial (ZMod p)) :=
    Multiset.replicate r P.1 + u.1
  have hfac :
      ∀ q ∈ sm, Irreducible q ∧ q.Monic := by
    intro q hq
    rcases Multiset.mem_add.mp hq with hq | hq
    · have hqp : q = P.1 :=
        (Multiset.mem_replicate.mp hq).2
      subst q
      exact ⟨P.2.2.1, P.2.1⟩
    · exact u.2.1 q hq
  have hdeg :
      (sm.map Polynomial.natDegree).sum = n := by
    dsimp [sm]
    simp only [Multiset.map_add, Multiset.map_replicate,
      Multiset.sum_add, Multiset.sum_replicate]
    rw [Nat.nsmul_eq_mul, u.2.2, hrd]
    have hjle : j.1 + 1 ≤ n := by omega
    omega
  let s : FactorData p n := ⟨sm, hfac, hdeg⟩
  have hmem : P.1 ∈ s.1.toFinset := by
    apply Multiset.mem_toFinset.mpr
    apply Multiset.mem_add.mpr
    exact Or.inl (Multiset.mem_replicate.mpr ⟨hrne, rfl⟩)
  let qsub : {q : Polynomial (ZMod p) // q ∈ s.1.toFinset} :=
    ⟨P.1, hmem⟩
  have hcount : r - 1 < s.1.count P.1 := by
    dsimp [s, sm]
    rw [Multiset.count_add, Multiset.count_replicate_self]
    omega
  exact ⟨s, qsub, ⟨r - 1, hcount⟩⟩

noncomputable def pointedToPrimePower
    (p n : ℕ) [Fact p.Prime] :
    PointedFactorData p n → PrimePowerDecomp p n := by
  rintro ⟨s, qsub, k⟩
  let q := qsub.1
  have hq : q ∈ s.1 := by
    exact Multiset.mem_toFinset.mp qsub.2
  have hqfac := s.2.1 q hq
  have hdpos : 0 < q.natDegree := hqfac.1.natDegree_pos
  let r := k.1 + 1
  have hrcount : r ≤ s.1.count q := by
    simp [r, q]
  have hrep : Multiset.replicate r q ≤ s.1 :=
    Multiset.le_count_iff_replicate_le.mp hrcount
  let um : Multiset (Polynomial (ZMod p)) :=
    s.1 - Multiset.replicate r q
  have hadd : Multiset.replicate r q + um = s.1 := by
    dsimp [um]
    exact add_tsub_cancel_of_le hrep
  have hjle : r * q.natDegree ≤ n := by
    have hsdeg := s.2.2
    rw [← hadd] at hsdeg
    simp only [Multiset.map_add, Multiset.map_replicate,
      Multiset.sum_add, Multiset.sum_replicate,
      Nat.nsmul_eq_mul] at hsdeg
    omega
  have hjpos : 0 < r * q.natDegree := Nat.mul_pos (by
    dsimp [r]; omega) hdpos
  let jval := r * q.natDegree
  let j : Fin n := ⟨jval - 1, by
    dsimp [jval]
    omega⟩
  have hj1 : j.1 + 1 = jval := by
    dsimp [j, jval]
    omega
  let P : RelevantIrred p (j.1 + 1) := by
    refine ⟨q, hqfac.2, hqfac.1, ?_⟩
    rw [hj1]
    exact dvd_mul_left q.natDegree r
  have hufac :
      ∀ a ∈ um, Irreducible a ∧ a.Monic := by
    intro a ha
    have ha' : a ∈ s.1 := by
      rw [← hadd]
      exact Multiset.mem_add.mpr (Or.inr ha)
    exact s.2.1 a ha'
  have hudeg :
      (um.map Polynomial.natDegree).sum =
        n - (j.1 + 1) := by
    have hsdeg := s.2.2
    rw [← hadd] at hsdeg
    simp only [Multiset.map_add, Multiset.map_replicate,
      Multiset.sum_add, Multiset.sum_replicate,
      Nat.nsmul_eq_mul] at hsdeg
    rw [hj1]
    omega
  let u : FactorData p (n - (j.1 + 1)) :=
    ⟨um, hufac, hudeg⟩
  exact ⟨j, P, u⟩



theorem pointed_primePower_left
    (p n : ℕ) [Fact p.Prime]
    (z : PrimePowerDecomp p n) :
    pointedToPrimePower p n (primePowerToPointed p n z) = z := by
  rcases z with ⟨j, P, u⟩
  let out :=
    pointedToPrimePower p n
      (primePowerToPointed p n ⟨j, (P, u)⟩)
  have hdpos : 0 < P.1.natDegree := P.2.2.1.natDegree_pos
  have hdvd : P.1.natDegree ∣ j.1 + 1 := P.2.2.2
  have hqpos : 0 < (j.1 + 1) / P.1.natDegree := by
    apply Nat.div_pos
    · exact Nat.le_of_dvd (by omega) hdvd
    · exact hdpos
  have hqone : 1 ≤ (j.1 + 1) / P.1.natDegree := by omega
  have hmul :
      ((j.1 + 1) / P.1.natDegree) * P.1.natDegree = j.1 + 1 :=
    Nat.div_mul_cancel hdvd
  have hidx :
      (((j.1 + 1) / P.1.natDegree - 1 + 1) *
          P.1.natDegree) - 1 = j.1 := by
    rw [Nat.sub_add_cancel hqone, hmul]
    omega
  have hidx1 :
      ((((j.1 + 1) / P.1.natDegree - 1 + 1) *
          P.1.natDegree) - 1) + 1 = j.1 + 1 := by
    rw [hidx]
  have hres :
      (Multiset.replicate ((j.1 + 1) / P.1.natDegree) P.1 + u.1) -
          Multiset.replicate ((j.1 + 1) / P.1.natDegree) P.1 = u.1 := by
    exact add_tsub_cancel_left _ _
  have hrepQ :
      Multiset.replicate ((j.1 + 1) / P.1.natDegree) P.1 =
        P.1 ::ₘ Multiset.replicate
          ((j.1 + 1) / P.1.natDegree - 1) P.1 := by
    calc
      Multiset.replicate ((j.1 + 1) / P.1.natDegree) P.1 =
          Multiset.replicate
            (((j.1 + 1) / P.1.natDegree - 1) + 1) P.1 := by
              rw [Nat.sub_add_cancel hqone]
      _ = _ := Multiset.replicate_succ _ _
  have hres' :
      (Multiset.replicate ((j.1 + 1) / P.1.natDegree) P.1 + u.1).erase P.1 -
          Multiset.replicate ((j.1 + 1) / P.1.natDegree - 1) P.1 = u.1 := by
    simp [hrepQ]
  have hj : out.1 = j := by
    apply Fin.ext
    dsimp [out]
    simp [primePowerToPointed, pointedToPrimePower,
      Nat.sub_add_cancel hqone, hmul]
  have hPval : out.2.1.1 = P.1 := by
    dsimp [out]
    simp [primePowerToPointed, pointedToPrimePower]
  have hUval : out.2.2.1 = u.1 := by
    dsimp [out]
    simpa [primePowerToPointed, pointedToPrimePower,
      Nat.sub_add_cancel hqone, hmul, hidx, hidx1] using hres'
  have hjval : out.1.1 = j.1 := congrArg Fin.val hj
  have hpPred :
      ∀ Q : Polynomial (ZMod p),
        (Q.Monic ∧ Irreducible Q ∧ Q.natDegree ∣ out.1.1 + 1) ↔
        (Q.Monic ∧ Irreducible Q ∧ Q.natDegree ∣ j.1 + 1) := by
    intro Q
    rw [hjval]
  have huPred :
      ∀ sm : Multiset (Polynomial (ZMod p)),
        ((∀ q ∈ sm, Irreducible q ∧ q.Monic) ∧
          (sm.map Polynomial.natDegree).sum = n - (out.1.1 + 1)) ↔
        ((∀ q ∈ sm, Irreducible q ∧ q.Monic) ∧
          (sm.map Polynomial.natDegree).sum = n - (j.1 + 1)) := by
    intro sm
    rw [hjval]
  have hP : out.2.1 ≍ P := by
    exact (Subtype.heq_iff_coe_eq hpPred).2 hPval
  have hU : out.2.2 ≍ u := by
    exact (Subtype.heq_iff_coe_eq huPred).2 hUval
  have hsnd : out.2 ≍ (P, u) :=
    prod_heq_of_heq hP hU
  exact Sigma.ext hj hsnd

theorem primePower_pointed_left
    (p n : ℕ) [Fact p.Prime]
    (z : PointedFactorData p n) :
    primePowerToPointed p n (pointedToPrimePower p n z) = z := by
  rcases z with ⟨s, q, k⟩
  let out :=
    primePowerToPointed p n
      (pointedToPrimePower p n ⟨s, ⟨q, k⟩⟩)
  have hqmem : q.1 ∈ s.1 :=
    Multiset.mem_toFinset.mp q.2
  have hdpos : 0 < q.1.natDegree :=
    (s.2.1 q.1 hqmem).1.natDegree_pos
  have hrcount : k.1 + 1 ≤ s.1.count q.1 :=
    Nat.succ_le_of_lt k.2
  have hrep : Multiset.replicate (k.1 + 1) q.1 ≤ s.1 :=
    Multiset.le_count_iff_replicate_le.mp hrcount
  have hcancel :
      Multiset.replicate (k.1 + 1) q.1 +
          (s.1 - Multiset.replicate (k.1 + 1) q.1) = s.1 :=
    add_tsub_cancel_of_le hrep
  have hprodpos : 0 < (k.1 + 1) * q.1.natDegree :=
    Nat.mul_pos (by omega) hdpos
  have hsubadd :
      (k.1 + 1) * q.1.natDegree - 1 + 1 =
        (k.1 + 1) * q.1.natDegree :=
    Nat.sub_add_cancel (by omega)
  have hdiv :
      ((k.1 + 1) * q.1.natDegree) / q.1.natDegree =
        k.1 + 1 := by
    simpa [Nat.mul_comm] using Nat.mul_div_right (k.1 + 1) hdpos
  have hidx :
      (((k.1 + 1) * q.1.natDegree - 1 + 1) /
          q.1.natDegree) - 1 = k.1 := by
    rw [hsubadd, hdiv]
    omega
  have hsval :
      Multiset.replicate
          (((k.1 + 1) * q.1.natDegree - 1 + 1) /
            q.1.natDegree) q.1 +
        (s.1 - q.1 ::ₘ Multiset.replicate k.1 q.1) = s.1 := by
    rw [hsubadd, hdiv]
    simpa [Multiset.replicate_succ] using hcancel
  have hs : out.1 = s := by
    apply Subtype.ext
    dsimp [out]
    simpa [primePowerToPointed, pointedToPrimePower,
      hsubadd, hdiv, hidx] using hsval
  have hqval : out.2.1.1 = q.1 := by
    dsimp [out]
    simp [primePowerToPointed, pointedToPrimePower, hsubadd, hdiv]
  have hkval : out.2.2.1 = k.1 := by
    dsimp [out]
    simp [primePowerToPointed, pointedToPrimePower, hsubadd, hdiv]
  have hsvalFD : out.1.1 = s.1 := congrArg Subtype.val hs
  have hqPred :
      ∀ a : Polynomial (ZMod p),
        a ∈ out.1.1.toFinset ↔ a ∈ s.1.toFinset := by
    intro a
    rw [hsvalFD]
  have hQ : out.2.1 ≍ q := by
    exact (Subtype.heq_iff_coe_eq hqPred).2 hqval
  have hcount :
      out.1.1.count out.2.1.1 = s.1.count q.1 := by
    rw [hqval, hsvalFD]
  have hkPred :
      ∀ i : ℕ,
        i < out.1.1.count out.2.1.1 ↔
          i < s.1.count q.1 := by
    intro i
    rw [hcount]
  have hK : out.2.2 ≍ k := by
    exact (Fin.heq_ext_iff hcount).2 hkval
  have hsnd : out.2 ≍
      (⟨q, k⟩ :
        Σ q' : {a : Polynomial (ZMod p) // a ∈ s.1.toFinset},
          Fin (s.1.count q'.1)) :=
    @nested_sigma_heq
      (FactorData p n)
      (fun ss => {a : Polynomial (ZMod p) // a ∈ ss.1.toFinset})
      (fun ss qq => Fin (ss.1.count qq.1))
      out.1 s hs
      out.2.1 q hQ
      out.2.2 k hK
  exact Sigma.ext hs hsnd

noncomputable def primePowerPointedEquiv
    (p n : ℕ) [Fact p.Prime] :
    PrimePowerDecomp p n ≃ PointedFactorData p n where
  toFun := primePowerToPointed p n
  invFun := pointedToPrimePower p n
  left_inv := pointed_primePower_left p n
  right_inv := primePower_pointed_left p n


end KloostermanWeil.Carlitz
