/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module
public import Mathlib.RingTheory.Nullstellensatz

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.M2.DimsData
public import LeanPool.RoyStrongSix.M2.Pairing

/-!
# Components without component theory (Roy §8.4.1, first half)

Everything is phrased with prime ideals and the bridge `hdim + ht = card σ`.

* `hdim_radical`, `exists_prime_hdim`, **`mem_minimalPrimes_of_hdim`**: a prime `p ⊇ L` with
  `hdim p = hdim L` is a minimal prime of `L` (strictness of `hdim` along primes).
* `vanish_zeros_eq` (Nullstellensatz on `G`, `K` algebraically closed): `I(Z(L)) = √L` for `I_G ≤
L`.
* `hdim_vanish_cosets`: a finite union of translates of `E` has the Hilbert dimension of `E`.
* **`component`** (Roy §8.4.1): let `L = I_G + (gens)`, and `p ⊇ L` prime with `hdim p = hdim L`,
  `V = Z(p)`. Then `G_V = {h : hV ⊆ V}` is an algebraic subgroup, and the zero set of
  `{P ∘ τ_v : P ∈ gens, v ∈ V}` is covered by finitely many cosets of `G_V`.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module Submodule StrongSix.Thm1

namespace StrongSix.M2

/-! ### Height and Hilbert dimension -/

section Generic

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type*} [Field K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (β : σ → ι) (D : ι → ℕ)

omit [DecidableEq σ] [Fintype ι] in
theorem height_eq_sub [Finite ι] (hD : ∀ i, 1 ≤ D i) {L : Ideal (MvPolynomial σ K)} (hL : L ≠ ⊤) :
    (hdata β D K L).1 ≤ Fintype.card σ ∧
      L.height = ((Fintype.card σ - (hdata β D K L).1 : ℕ) : ℕ∞) := by
  classical
  let : DecidableEq σ := Classical.decEq σ
  let : Fintype ι := Fintype.ofFinite ι
  have h := hdim_add_height_eq β D hD hL
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top hL)
  rw [← hn] at h
  have h' : (hdata β D K L).1 + n = Fintype.card σ := by exact_mod_cast h
  refine ⟨by omega, ?_⟩
  rw [← hn]
  exact_mod_cast (by omega : n = Fintype.card σ - (hdata β D K L).1)

omit [DecidableEq σ] [Fintype ι] in
theorem hdim_le_of_height_le [Finite ι] (hD : ∀ i, 1 ≤ D i) {L L' : Ideal (MvPolynomial σ K)}
    (hL : L ≠ ⊤) (hL' : L' ≠ ⊤) (h : L.height ≤ L'.height) :
    (hdata β D K L').1 ≤ (hdata β D K L).1 := by
  classical
  let : DecidableEq σ := Classical.decEq σ
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨h1, e1⟩ := height_eq_sub β D hD hL
  obtain ⟨h2, e2⟩ := height_eq_sub β D hD hL'
  rw [e1, e2] at h
  have := Nat.cast_le.mp h
  omega

omit [DecidableEq σ] [Fintype ι] in
theorem hdim_radical [Finite ι] (hD : ∀ i, 1 ≤ D i) {L : Ideal (MvPolynomial σ K)} (hL : L ≠ ⊤) :
    (hdata β D K L.radical).1 = (hdata β D K L).1 := by
  classical
  let : DecidableEq σ := Classical.decEq σ
  let : Fintype ι := Fintype.ofFinite ι
  have hr : L.radical ≠ ⊤ := fun h => hL (Ideal.radical_eq_top.mp h)
  have : L.radical.height = L.height := by
    rw [Ideal.height_eq_inf_minimalPrimes, Ideal.height_eq_inf_minimalPrimes L,
      Ideal.radical_minimalPrimes]
  exact le_antisymm (hdim_le_of_height_le β D hD hL hr this.ge)
    (hdim_le_of_height_le β D hD hr hL this.le)

omit [DecidableEq σ] [Fintype ι] in
theorem exists_prime_hdim [Finite ι] (hD : ∀ i, 1 ≤ D i) {L : Ideal (MvPolynomial σ K)}
    (hL : L ≠ ⊤) :
    ∃ p : Ideal (MvPolynomial σ K), p.IsPrime ∧ L ≤ p ∧
      (hdata β D K p).1 = (hdata β D K L).1 := by
  classical
  let : DecidableEq σ := Classical.decEq σ
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top hL)
  obtain ⟨p, hp, hLp, hpn⟩ := Ideal.exists_isPrime_height_eq hn.symm
  exact ⟨p, hp, hLp, le_antisymm (hdim_le_of_height_le β D hD hL hp.ne_top (by rw [hpn, hn]))
    (hdim_le_of_height_le β D hD hp.ne_top hL (by rw [hpn, hn]))⟩

omit [DecidableEq σ] [Fintype ι] in
/-- **A prime over `L` with the Hilbert dimension of `L` is minimal over `L`.** -/
theorem mem_minimalPrimes_of_hdim [Finite ι] (hD : ∀ i, 1 ≤ D i) {L p : Ideal (MvPolynomial σ K)}
    [hp : p.IsPrime] (hLp : L ≤ p) (h : (hdata β D K p).1 = (hdata β D K L).1) :
    p ∈ L.minimalPrimes := by
  classical
  let : DecidableEq σ := Classical.decEq σ
  let : Fintype ι := Fintype.ofFinite ι
  have hL : L ≠ ⊤ := ne_top_of_le_ne_top hp.ne_top hLp
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le hLp
  have hqprime : q.IsPrime := hq.1.1
  have hqh : L.height ≤ q.height := by
    rw [Ideal.height_eq_inf_minimalPrimes L]; exact iInf₂_le q hq
  have h1 := hdim_le_of_height_le β D hD hL hqprime.ne_top hqh
  rcases eq_or_lt_of_le hqp with rfl | hlt
  · exact hq
  · have := hdim_lt_of_lt β D K hD (q := q) (q' := p) hp.ne_top hlt
    omega

omit [DecidableEq σ] in
omit [Fintype ι] in
theorem hdata_congr [Finite ι] {J J' : Ideal (MvPolynomial σ K)} (hJ : J ≠ ⊤) (hJ' : J' ≠ ⊤)
    (h : ∀ t, hfun β D K J t = hfun β D K J' t) : hdata β D K J = hdata β D K J' := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  refine (hdata_eq β D K hJ' ?_).symm
  have := hdata_spec β D K hJ
  simp only [h] at this
  exact this

end Generic

variable {K : Type*} [Field K] [CharZero K] {d0 d1 : ℕ}

local notation "B" => MvPolynomial (V3 d0 d1) K

/-! ### The Nullstellensatz on `G` -/

omit [CharZero K] in
theorem gmul_comm (g h : GPt K d0 d1) : gmul g h = gmul h g := by
  simp only [gmul, add_comm, mul_comm]

omit [CharZero K] in
theorem IG_le_vanish' (E : Set (GPt K d0 d1)) : (IG : Ideal B) ≤ vanish E :=
  IG_le_vanish.trans fun _ hP g _ => hP g (Set.mem_univ g)

omit [CharZero K] in
theorem exists_pt_of_mem_zeroLocus {L : Ideal B} (hL : IG ≤ L) {x : V3 d0 d1 → K}
    (hx : x ∈ zeroLocus K L) : ∃ g : GPt K d0 d1, pt g = x := by
  have hyz : ∀ j, x (Sum.inr (Sum.inl j)) * x (Sum.inr (Sum.inr j)) = 1 := by
    intro j
    have := hx _ (hL (YZ_mem_IG j))
    simpa [sub_eq_zero] using this
  refine ⟨(fun k => x (Sum.inl k), fun j => Units.mkOfMulEqOne _ _ (hyz j)), ?_⟩
  funext v
  rcases v with k | j | j
  · rfl
  · rfl
  · simpa [pt] using inv_eq_of_mul_eq_one_right (hyz j)

omit [CharZero K] in
/-- **Hilbert's Nullstellensatz on `G`.** -/
theorem vanish_zeros_eq [IsAlgClosed K] {L : Ideal B} (hL : IG ≤ L) :
    vanish (zeros (L : Set B)) = L.radical := by
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := K)]
  ext P
  constructor
  · intro hP x hx
    obtain ⟨g, rfl⟩ := exists_pt_of_mem_zeroLocus hL hx
    exact hP g fun Q hQ => hx Q hQ
  · intro hP g hg
    exact hP (pt g) (fun Q hQ => hg Q hQ)

omit [CharZero K] in
theorem vanish_zeros_prime [IsAlgClosed K] {p : Ideal B} [hp : p.IsPrime] (h : IG ≤ p) :
    vanish (zeros (p : Set B)) = p := by
  rw [vanish_zeros_eq h, hp.radical]

omit [CharZero K] in
theorem vanish_empty : vanish (∅ : Set (GPt K d0 d1)) = ⊤ :=
  eq_top_iff.mpr fun _ _ _ hg => absurd hg (Set.notMem_empty _)

omit [CharZero K] in
theorem zeros_nonempty [IsAlgClosed K] {L : Ideal B} (hL : IG ≤ L) (hne : L ≠ ⊤) :
    (zeros (L : Set B)).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have := vanish_zeros_eq hL
  rw [h, vanish_empty] at this
  exact hne (Ideal.radical_eq_top.mp this.symm)

/-! ### Finite unions of translates -/

variable (D : Fin 2 → ℕ)

theorem hfun_vanish_biUnion_le (E : Set (GPt K d0 d1)) (R : Finset (GPt K d0 d1)) (t : ℕ) :
    hfun blk D K (vanish (⋃ a ∈ R, gtransl a E)) t ≤ R.card * hfun blk D K (vanish E) t := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Finset.card_empty,
      zero_mul, vanish_empty]
    unfold hfun
    rw [inf_eq_right.mpr (fun x _ => by simp), Nat.sub_self]
  | insert a R ha ih =>
    rw [Finset.set_biUnion_insert, Finset.card_insert_of_notMem ha]
    calc hfun blk D K (vanish (gtransl a E ∪ ⋃ x ∈ R, gtransl x E)) t
        ≤ hfun blk D K (vanish (gtransl a E)) t + hfun blk D K (vanish (⋃ x ∈ R, gtransl x E)) t :=
          hfun_union_le D _ _ t
      _ ≤ hfun blk D K (vanish E) t + R.card * hfun blk D K (vanish E) t := by
          rw [hfun_vanish_transl]; omega
      _ = (R.card + 1) * hfun blk D K (vanish E) t := by ring

/-- A nonempty finite union of translates of `E` has the Hilbert dimension of `E`. -/
theorem hdim_vanish_cosets (E : Set (GPt K d0 d1)) (hE : E.Nonempty) (R : Finset (GPt K d0 d1))
    (hR : R.Nonempty) :
    (hdata blk D K (vanish (⋃ a ∈ R, gtransl a E))).1 = (hdata blk D K (vanish E)).1 := by
  obtain ⟨a, ha⟩ := hR
  obtain ⟨e, he⟩ := hE
  have hUne : vanish (⋃ a ∈ R, gtransl a E) ≠ ⊤ := one_notMem_vanish
    ⟨gmul a e, Set.mem_biUnion ha ⟨e, he, rfl⟩⟩
  have hEne : vanish E ≠ ⊤ := one_notMem_vanish ⟨e, he⟩
  have hf := hdata_spec blk D K hEne
  have hg := hdata_spec blk D K hUne
  -- lower bound: `I(⋃) ⊆ I(aE)`
  have hlow : ∀ t, hfun blk D K (vanish E) t ≤ hfun blk D K (vanish (⋃ a ∈ R, gtransl a E)) t := by
    intro t
    rw [← hfun_vanish_transl D a E t]
    exact hfun_mono blk D K (J := vanish (⋃ a ∈ R, gtransl a E)) (J' := vanish (gtransl a E))
      (fun P hP g hg => hP g (Set.mem_biUnion ha hg)) t
  have hcard : (R.card : ℤ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨a, ha⟩).ne'
  have hfs := hf.smul hcard
  have c1 := hf.compare hg (Filter.Eventually.of_forall fun t => by exact_mod_cast hlow t)
    (Filter.Eventually.of_forall fun _ => by positivity)
  have c2 := hg.compare hfs (Filter.Eventually.of_forall fun t => by
      exact_mod_cast hfun_vanish_biUnion_le D E R t)
    (Filter.Eventually.of_forall fun _ => by positivity)
  omega

/-! ### Roy's component argument -/

/-- The stabilizer `{h : hV ⊆ V}`. -/
def stabG (V : Set (GPt K d0 d1)) : Set (GPt K d0 d1) := {h | ∀ v ∈ V, gmul h v ∈ V}

omit [CharZero K] in
theorem ginv_gmul_cancel (a g : GPt K d0 d1) : gmul (ginv a) (gmul a g) = g := by
  rw [← gmul_assoc, gmul_ginv, gzero_gmul]

omit [CharZero K] in
theorem gmul_ginv_cancel (a g : GPt K d0 d1) : gmul a (gmul (ginv a) g) = g := by
  rw [← gmul_assoc, gmul_ginv', gzero_gmul]

omit [CharZero K] in
theorem mem_vanish_gtransl_iff {h : GPt K d0 d1} {V : Set (GPt K d0 d1)} {P : B} :
    P ∈ vanish (gtransl h V) ↔ transl h P ∈ vanish V := transl_mem_vanish.symm

section Comp

variable [IsAlgClosed K] {p : Ideal (MvPolynomial (V3 d0 d1) K)} [hp : p.IsPrime] (hIGp : IG (K
  := K) (d0 := d0) (d1 := d1) ≤ p)
include hIGp

omit [CharZero K] in
theorem vanish_gtransl_isPrime (h : GPt K d0 d1) :
    (vanish (gtransl h (zeros (p : Set B)))).IsPrime := by
  have e : vanish (gtransl h (zeros (p : Set B))) = Ideal.comap (transl h : B →+* B) p := by
    ext P
    rw [mem_vanish_gtransl_iff, vanish_zeros_prime hIGp]
    rfl
  rw [e]; exact Ideal.comap_isPrime _ _

omit [IsAlgClosed K] hp hIGp in
omit [CharZero K] in
/-- Translates of `Z(p)` are closed. -/
theorem zeros_vanish_gtransl (h : GPt K d0 d1) :
    zeros (vanish (gtransl h (zeros (p : Set B))) : Set B) = gtransl h (zeros (p : Set B)) := by
  apply le_antisymm
  · intro g hg
    refine ⟨gmul (ginv h) g, fun Q hQ => ?_, gmul_ginv_cancel h g⟩
    have hmem : transl (ginv h) Q ∈ vanish (gtransl h (zeros (p : Set B))) := by
      rintro _ ⟨v, hv, rfl⟩
      rw [eval_transl, ginv_gmul_cancel]
      exact hv Q hQ
    have := hg _ hmem
    rwa [eval_transl] at this
  · intro g hg P hP
    exact hP g hg

theorem hdim_vanish_gtransl (h : GPt K d0 d1) :
    (hdata blk D K (vanish (gtransl h (zeros (p : Set B))))).1 = (hdata blk D K p).1 := by
  have hne : (zeros (p : Set B)).Nonempty := zeros_nonempty hIGp hp.ne_top
  obtain ⟨v, hv⟩ := hne
  have h1 : vanish (gtransl h (zeros (p : Set B))) ≠ ⊤ := one_notMem_vanish ⟨gmul h v, v, hv, rfl⟩
  have h2 : vanish (zeros (p : Set B)) ≠ ⊤ := one_notMem_vanish ⟨v, hv⟩
  rw [hdata_congr blk D h1 h2 (fun t => hfun_vanish_transl D h _ t), vanish_zeros_prime hIGp]

/-- If `hV ⊆ V` then `hV = V`. -/
theorem gtransl_eq_of_subset (hD : ∀ i, 1 ≤ D i) {h : GPt K d0 d1}
    (hsub : gtransl h (zeros (p : Set B)) ⊆ zeros (p : Set B)) :
    gtransl h (zeros (p : Set B)) = zeros (p : Set B) := by
  have := vanish_gtransl_isPrime hIGp h
  have hle : p ≤ vanish (gtransl h (zeros (p : Set B))) := fun P hP g hg => hsub hg P hP
  have heq : p = vanish (gtransl h (zeros (p : Set B))) := by
    rcases eq_or_lt_of_le hle with e | hlt
    · exact e
    · have := hdim_lt_of_lt blk D K hD (q := p) (Ideal.IsPrime.ne_top inferInstance) hlt
      rw [hdim_vanish_gtransl D hIGp h] at this
      omega
  rw [← zeros_vanish_gtransl h, ← heq]

theorem stabG_isSubgroup (hD : ∀ i, 1 ≤ D i) : IsSubgroupG (stabG (zeros (p : Set B))) where
  one_mem v hv := by rwa [gzero_gmul]
  mul_mem g hg h hh v hv := by rw [gmul_assoc]; exact hg _ (hh v hv)
  inv_mem g hg v hv := by
    have heq := gtransl_eq_of_subset D hIGp hD (h := g) (by rintro _ ⟨u, hu, rfl⟩; exact hg u hu)
    rw [← heq] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    rwa [ginv_gmul_cancel]

omit [IsAlgClosed K] hp hIGp in
omit [CharZero K] in
theorem stabG_eq_zeros :
    stabG (zeros (p : Set B)) =
      zeros {Q | ∃ v ∈ zeros (p : Set B), ∃ P ∈ p, Q = transl v P} := by
  ext h
  constructor
  · rintro hh _ ⟨v, hv, P, hP, rfl⟩
    rw [eval_transl, gmul_comm]
    exact hh v hv P hP
  · intro hh v hv P hP
    have := hh _ ⟨v, hv, P, hP, rfl⟩
    rwa [eval_transl, gmul_comm] at this

/-- **Roy's component step.** -/
theorem component (hD : ∀ i, 1 ≤ D i) {L : Ideal B} (gens : Set B) (hLg : L = IG ⊔ Ideal.span gens)
    (_ : L ≤ p) (hdim : (hdata blk D K p).1 = (hdata blk D K L).1) :
    ∃ R : Finset (GPt K d0 d1), (∀ a ∈ R, ∀ v ∈ zeros (p : Set B), ∀ P ∈ gens,
        eval (pt (gmul a v)) P = 0) ∧
      zeros {Q | ∃ P ∈ gens, ∃ v ∈ zeros (p : Set B), Q = transl v P} ⊆
        ⋃ a ∈ R, gtransl a (stabG (zeros (p : Set B))) := by
  classical
  set V := zeros (p : Set B)
  set Z := zeros {Q | ∃ P ∈ gens, ∃ v ∈ V, Q = transl v P}
  -- `I(hV)` is a minimal prime of `L` for `h ∈ Z`
  have hmin : ∀ h ∈ Z, vanish (gtransl h V) ∈ L.minimalPrimes := by
    intro h hh
    have := vanish_gtransl_isPrime hIGp h
    refine mem_minimalPrimes_of_hdim blk D hD ?_ ?_
    · rw [hLg]
      refine sup_le (IG_le_vanish' _) (Ideal.span_le.mpr fun P hP => ?_)
      rintro _ ⟨v, hv, rfl⟩
      have := hh _ ⟨P, hP, v, hv, rfl⟩
      rwa [eval_transl, gmul_comm] at this
    · rw [hdim_vanish_gtransl D hIGp h, hdim]
  have hfinM : L.minimalPrimes.Finite := L.finite_minimalPrimes_of_isNoetherianRing
  let φ : GPt K d0 d1 → Ideal B := fun h => vanish (gtransl h V)
  have hfin : (φ '' Z).Finite := hfinM.subset (by rintro _ ⟨h, hh, rfl⟩; exact hmin h hh)
  have hrep : ∀ q ∈ φ '' Z, ∃ a ∈ Z, φ a = q := fun q hq => hq
  choose! rep hrepZ hrepφ using hrep
  refine ⟨hfin.toFinset.image rep, fun a ha v hv P hP => ?_, fun h hh => ?_⟩
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
    have hZ := hrepZ q ((Set.Finite.mem_toFinset _).mp hq)
    have := hZ _ ⟨P, hP, v, hv, rfl⟩
    rwa [eval_transl, gmul_comm] at this
  · have hq : φ h ∈ φ '' Z := ⟨h, hh, rfl⟩
    set a := rep (φ h)
    have haZ : a ∈ Z := hrepZ _ hq
    have haφ : φ a = φ h := hrepφ _ hq
    have hV : gtransl a V = gtransl h V := by
      rw [← zeros_vanish_gtransl a, ← zeros_vanish_gtransl h]
      exact congrArg (fun J : Ideal B => zeros (J : Set B)) haφ
    simp only [Set.mem_iUnion]
    refine ⟨a, Finset.mem_image.mpr ⟨φ h, (Set.Finite.mem_toFinset _).mpr hq, rfl⟩,
      gmul (ginv a) h, fun v hv => ?_, gmul_ginv_cancel a h⟩
    have : gmul h v ∈ gtransl a V := hV ▸ ⟨v, hv, rfl⟩
    obtain ⟨u, hu, hu'⟩ := this
    rw [gmul_assoc, ← hu', ginv_gmul_cancel]
    exact hu

omit [CharZero K] in
/-- If the stabilizer is all of `G`, then `L ⊆ I(G)`. -/
theorem le_vanish_univ_of_stabG {L : Ideal B} (hLp : L ≤ p)
    (h : stabG (zeros (p : Set B)) = Set.univ) : L ≤ vanish Set.univ := by
  obtain ⟨v0, hv0⟩ := zeros_nonempty hIGp hp.ne_top
  have hV : zeros (p : Set B) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    have hmem : gmul g (ginv v0) ∈ stabG (zeros (p : Set B)) := h ▸ Set.mem_univ _
    have := hmem v0 hv0
    rwa [gmul_assoc, gmul_ginv, gmul_comm, gzero_gmul] at this
  rw [← hV, vanish_zeros_prime hIGp]
  exact hLp

end Comp

end StrongSix.M2

end LeanPool
