/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module
public import Mathlib.RingTheory.KrullDimension.Polynomial

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.M2.Bridge

/-!
# Hilbert dimension versus height, lower bound and the bridge

* `height_isMaximal`: every maximal ideal of `K[σ]` has height `card σ`. The proof is by induction
on
  the number of variables, using `Polynomial.height_eq_height_add_one` and the Jacobson property.
* `card_le_hdim_add_height`: for a prime `p`, `card σ ≤ hdim p + ht p`. In the Cohen–Macaulay
local ring
  `A_m` (`m ⊇ p` maximal), `ht p + dim (A_m / p A_m) = dim A_m = card σ`. Every chain of primes of
  `A_m / p A_m` gives a strictly decreasing sequence of Hilbert dimensions below `hdim p`.
* **`hdim_add_height_eq`**: for every proper ideal `L`, `hdim L + ht L = card σ`.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module Submodule _root_.IsLocalRing

namespace StrongSix.M2

/-- Maximal ideals of `K[X₁, …, Xₙ]` have height `n`. -/
theorem height_isMaximal_fin (K : Type*) [Field K] :
    ∀ (n : ℕ) (m : Ideal (MvPolynomial (Fin n) K)), m.IsMaximal → m.height = n
  | 0, m, hm => by
    apply le_antisymm _ bot_le
    have h1 := Ideal.height_le_ringKrullDim_of_ne_top hm.ne_top
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
      at h1
    simpa using h1
  | n + 1, m, hm => by
    let e := (MvPolynomial.finSuccEquiv K n).toRingEquiv
    let M := m.map e
    have hM : M.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let p := M.comap (Polynomial.C : MvPolynomial (Fin n) K →+* Polynomial (MvPolynomial (Fin n) K))
    have hp : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing (P := M)
    have : M.LiesOver p := ⟨rfl⟩
    rw [← RingEquiv.height_map e m, Polynomial.height_eq_height_add_one p M,
      height_isMaximal_fin K n p hp]
    push_cast
    rfl

/-- Maximal ideals of `K[σ]` have height `card σ`. -/
theorem height_isMaximal {σ : Type*} [Fintype σ] (K : Type*) [Field K]
    (m : Ideal (MvPolynomial σ K)) [hm : m.IsMaximal] : m.height = Fintype.card σ := by
  let e := (renameEquiv K (Fintype.equivFin σ)).toRingEquiv
  rw [← RingEquiv.height_map e m]
  exact height_isMaximal_fin K _ _ (Ideal.map_isMaximal_of_equiv e)

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type*} [Field K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (β : σ → ι) (D : ι → ℕ)

local notation "A" => MvPolynomial σ K

omit [DecidableEq σ] in
omit [Fintype ι] in
/-- **Lower bound** for primes. -/
theorem card_le_hdim_add_height [Finite ι] (hD : ∀ i, 1 ≤ D i) (p : Ideal A) [hp : p.IsPrime] :
    (Fintype.card σ : ℕ∞) ≤ (hdata β D K p).1 + p.height := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hp.ne_top
  let Rm := Localization.AtPrime m
  have : IsCohenMacaulayLocalRing Rm :=
    (isCohenMacaulayRing_def A).mp inferInstance m hm.isPrime
  have disj : Disjoint (m.primeCompl : Set A) (p : Set A) :=
    Set.disjoint_left.mpr fun a ha hap => ha (hpm hap)
  let P := p.map (algebraMap A Rm)
  have : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl Rm p hp disj
  have hform := Ideal.primeHeight_add_ringKrullDim_quotient_eq_ringKrullDim P
  rw [← Ideal.height_eq_primeHeight, IsLocalization.height_map_of_disjoint m.primeCompl p disj,
    IsLocalization.AtPrime.ringKrullDim_eq_height m Rm, height_isMaximal K m] at hform
  -- `dim (A_m / P) ≤ hdim p`
  let φ : A →+* Rm ⧸ P := (Ideal.Quotient.mk P).comp (algebraMap A Rm)
  have hφinj : ∀ Q : Ideal (Rm ⧸ P), Ideal.map φ (Ideal.comap φ Q) = Q := by
    intro Q
    have h1 : Ideal.comap φ Q = Ideal.comap (algebraMap A Rm) (Ideal.comap (Ideal.Quotient.mk P)
      Q) :=
      by rw [Ideal.comap_comap]
    rw [h1, ← Ideal.map_map, IsLocalization.map_under m.primeCompl Rm,
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have hple : ∀ Q : Ideal (Rm ⧸ P), p ≤ Ideal.comap φ Q := by
    intro Q x hx
    have : algebraMap A Rm x ∈ P := Ideal.mem_map_of_mem _ hx
    simp only [Ideal.mem_comap, φ, RingHom.coe_comp, Function.comp_apply]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr this]
    exact Q.zero_mem
  let g : PrimeSpectrum (Rm ⧸ P) → ℕ := fun Q => (hdata β D K (Ideal.comap φ Q.asIdeal)).1
  have hg : StrictAnti g := by
    intro Q Q' hlt
    have hle : Ideal.comap φ Q.asIdeal ≤ Ideal.comap φ Q'.asIdeal := Ideal.comap_mono hlt.le
    have hne : Ideal.comap φ Q.asIdeal ≠ Ideal.comap φ Q'.asIdeal := fun h => by
      apply hlt.ne
      ext1
      rw [← hφinj Q.asIdeal, ← hφinj Q'.asIdeal, h]
    have : (Ideal.comap φ Q.asIdeal).IsPrime := Ideal.comap_isPrime φ Q.asIdeal
    exact hdim_lt_of_lt β D K hD (Ideal.comap_isPrime φ Q'.asIdeal).ne_top (lt_of_le_of_ne hle hne)
  have hgle : ∀ Q, g Q ≤ (hdata β D K p).1 := by
    intro Q
    rcases hdata_le_of_le β D K (hple Q.asIdeal) (Ideal.comap_isPrime φ Q.asIdeal).ne_top with
      h | ⟨h, -⟩ <;> simp only [g] <;> omega
  have hdimle : ringKrullDim (Rm ⧸ P) ≤ ((hdata β D K p).1 : ℕ∞) := by
    unfold ringKrullDim Order.krullDim
    refine iSup_le fun s => ?_
    have key : ∀ i : ℕ, ∀ hi : i < s.length + 1, g (s ⟨i, hi⟩) + i ≤ g (s 0) := by
      intro i
      induction i with
      | zero => intro _; simp
      | succ i ih =>
        intro hi
        have h1 := ih (by omega)
        have h2 : g (s ⟨i + 1, hi⟩) < g (s ⟨i, by omega⟩) :=
          hg (s.strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self i)))
        omega
    have h1 := key s.length (Nat.lt_succ_self _)
    have h3 := hgle (s 0)
    have : s.length ≤ (hdata β D K p).1 := by omega
    exact_mod_cast this
  -- combine
  have key : ((Fintype.card σ : ℕ∞) : WithBot ℕ∞) ≤
      ((p.height + (hdata β D K p).1 : ℕ∞) : WithBot ℕ∞) := by
    rw [← hform, WithBot.coe_add]
    gcongr
  rw [add_comm]
  exact_mod_cast key

omit [DecidableEq σ] [Fintype ι] in
/-- **The bridge:** `hdim L + ht L = card σ` for every proper ideal `L`. -/
theorem hdim_add_height_eq [Finite ι] (hD : ∀ i, 1 ≤ D i) {L : Ideal A} (hL : L ≠ ⊤) :
    ((hdata β D K L).1 : ℕ∞) + L.height = Fintype.card σ := by
  classical
  let : DecidableEq σ := Classical.decEq σ
  let : Fintype ι := Fintype.ofFinite ι
  apply le_antisymm (hdim_add_height_le β D hD hL)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top hL)
  obtain ⟨p, hp, hLp, hpn⟩ := Ideal.exists_isPrime_height_eq hn.symm
  have h1 := card_le_hdim_add_height β D hD p
  have h2 : (hdata β D K p).1 ≤ (hdata β D K L).1 := by
    rcases hdata_le_of_le β D K hLp hp.ne_top with h | ⟨h, -⟩ <;> omega
  rw [hpn] at h1
  rw [← hn]
  calc (Fintype.card σ : ℕ∞) ≤ (hdata β D K p).1 + n := h1
    _ ≤ (hdata β D K L).1 + n := by gcongr

end StrongSix.M2

end LeanPool
