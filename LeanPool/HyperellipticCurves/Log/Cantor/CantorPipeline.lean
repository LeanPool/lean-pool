/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Cantor.CantorAdd

/-!
# The Cantor pipeline: composition and reduction as functions of the data

The identities of `LeanPool.HyperellipticCurves.Log.Cantor.CantorAdd` packaged as *named operations*
on
Mumford data pairs, ready to be iterated in the construction of the translated group law `def:Ftau`:

* `ChabautyColeman.cantorCofactor`: the exact cofactor `(v² - f) /ₘ u`;
* `ChabautyColeman.cantorCompose`: composition with a Bézout certificate, `v`-part reduced
  modulo the product;
* `ChabautyColeman.cantorReduce`: the normalized reduction step with a leading-coefficient
  inverse certificate `c * (cantorCofactor f u v).leadingCoeff = 1`.

Each operation preserves the Mumford-datum conditions (monic, degree bound, `u ∣ v² - f`),
comes with degree bookkeeping, and over a field computes the expected ideal class
(`ChabautyColeman.mk0_cantorCompose`, `ChabautyColeman.mk0_cantorReduce`); the four-stage
pipeline compose–reduce–compose–reduce carries the invariants through
(`ChabautyColeman.cantorPipeline_stage_invariants`) and computes the class `c₁ + c₂ - τ`
(`ChabautyColeman.mk0_cantorPipeline`).

All operations commute with base change along any ring homomorphism, given the monicity
certificates (`ChabautyColeman.map_cantorCompose`, `ChabautyColeman.map_cantorReduce`,
`ChabautyColeman.map_reduceCert`) — this is what specializes the `F_τ` pipeline both to the
residue field (the center analysis) and at points (evaluation).  A reduction certificate over
the residue field whose cofactor has the generic degree lifts
(`ChabautyColeman.exists_reduceCert_map`).
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section Pipeline

variable {R : Type*} [CommRing R] (f : R[X])

/-- The exact cofactor of a Mumford datum: `(v² - f) /ₘ u`. When `u` is monic and divides
`v² - f`, this is the exact quotient (`ChabautyColeman.cantorCofactor_spec`). -/
noncomputable def cantorCofactor (u v : R[X]) : R[X] := (v ^ 2 - f) /ₘ u

theorem cantorCofactor_spec {u v : R[X]} (hu : u.Monic) (hdvd : u ∣ v ^ 2 - f) :
    v ^ 2 - f = u * cantorCofactor f u v := by
  have h0 : (v ^ 2 - f) %ₘ u = 0 := (modByMonic_eq_zero_iff_dvd hu).mpr hdvd
  have := modByMonic_add_div (v ^ 2 - f) u
  rw [h0, zero_add] at this
  exact this.symm

/-- **Leading coefficient and degree of the cofactor** of a Mumford datum on a curve of odd
degree `2n+1`: since `deg V < deg U` the square `V²` cannot reach `deg f`, so `V² - f` has
leading coefficient `-1` and degree `2n+1`, and the cofactor of a monic `U` of degree `k`
has leading coefficient `-1` and degree `2n+1-k`. -/
theorem leadingCoeff_natDegree_cantorCofactor [Nontrivial R] {u v : R[X]} {n k : ℕ}
    (hf : f.Monic) (hfdeg : f.natDegree = 2 * n + 1) (hu : u.Monic) (hudeg : u.natDegree = k)
    (hdvd : u ∣ v ^ 2 - f) (hv : v.degree < u.degree) (hk : k ≤ n + 1) :
    (cantorCofactor f u v).leadingCoeff = -1
      ∧ (cantorCofactor f u v).natDegree + k = 2 * n + 1 := by
  have hspec := cantorCofactor_spec f hu hdvd
  -- the square stays below `f` in degree
  have hV2deg : (v ^ 2).degree < f.degree := by
    rcases eq_or_ne v 0 with rfl | h0
    · rw [zero_pow two_ne_zero, degree_zero]
      exact WithBot.bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr hf.ne_zero)
    · refine degree_lt_degree ?_
      have h1 : v.natDegree < u.natDegree := natDegree_lt_natDegree h0 hv
      have h2 : (v ^ 2).natDegree ≤ 2 * v.natDegree := natDegree_pow_le.trans (by lia)
      rw [hfdeg]
      lia
  have hV2nd : (v ^ 2).natDegree < f.natDegree := by
    rcases eq_or_ne (v ^ 2) 0 with h0 | h0
    · rw [h0, natDegree_zero, hfdeg]
      lia
    · exact natDegree_lt_natDegree h0 hV2deg
  have hlcsub : (v ^ 2 - f).leadingCoeff = -1 := by
    rw [leadingCoeff_sub_of_degree_lt' hV2deg, hf.leadingCoeff]
  have hndsub : (v ^ 2 - f).natDegree = 2 * n + 1 := by
    rw [natDegree_sub_eq_right_of_natDegree_lt hV2nd, hfdeg]
  have hlcW : (cantorCofactor f u v).leadingCoeff = -1 := by
    have h1 := congrArg leadingCoeff hspec
    rw [hlcsub, mul_comm, leadingCoeff_mul_monic hu] at h1
    exact h1.symm
  refine ⟨hlcW, ?_⟩
  have hlcne : u.leadingCoeff * (cantorCofactor f u v).leadingCoeff ≠ 0 := by
    rw [hu.leadingCoeff, one_mul, hlcW]
    exact neg_ne_zero.mpr one_ne_zero
  rw [← hudeg, add_comm, ← natDegree_mul' hlcne, ← hspec, hndsub]

/-- A Mumford datum stays a Mumford datum under reduction of `v` modulo `u`
(general-ring version of `ChabautyColeman.dvd_modByMonic_sq_sub`). -/
theorem dvd_modByMonic_sq_sub_of_dvd {u v : R[X]} (hdvd : u ∣ v ^ 2 - f) :
    u ∣ (v %ₘ u) ^ 2 - f := by
  have h1 : u ∣ (v %ₘ u) ^ 2 - v ^ 2 := by
    have : (v %ₘ u) ^ 2 - v ^ 2 = (v %ₘ u - v) * (v %ₘ u + v) := by ring
    rw [this]
    exact (dvd_modByMonic_sub v u).mul_right _
  have : (v %ₘ u) ^ 2 - f = ((v %ₘ u) ^ 2 - v ^ 2) + (v ^ 2 - f) := by ring
  rw [this]
  exact dvd_add h1 hdvd

/-- Cantor composition of two Mumford data with a Bézout certificate: the `u`-parts
multiply and the `v`-part is the certificate combination, reduced modulo the product. -/
noncomputable def cantorCompose (u₁ v₁ u₂ v₂ s₁ s₂ s₃ : R[X]) : R[X] × R[X] :=
  (u₁ * u₂, cantorV f u₁ v₁ u₂ v₂ s₁ s₂ s₃ %ₘ (u₁ * u₂))

theorem cantorCompose_fst (u₁ v₁ u₂ v₂ s₁ s₂ s₃ : R[X]) :
    (cantorCompose f u₁ v₁ u₂ v₂ s₁ s₂ s₃).1 = u₁ * u₂ := rfl

theorem cantorCompose_snd (u₁ v₁ u₂ v₂ s₁ s₂ s₃ : R[X]) :
    (cantorCompose f u₁ v₁ u₂ v₂ s₁ s₂ s₃).2
      = cantorV f u₁ v₁ u₂ v₂ s₁ s₂ s₃ %ₘ (u₁ * u₂) := rfl

/-- One Cantor reduction step with a leading-coefficient inverse certificate `c`: replace
`(u, v)` by the normalized cofactor datum. -/
noncomputable def cantorReduce (u v : R[X]) (c : R) : R[X] × R[X] :=
  (C c * cantorCofactor f u v, (-v) %ₘ (C c * cantorCofactor f u v))

theorem cantorReduce_fst (u v : R[X]) (c : R) :
    (cantorReduce f u v c).1 = C c * cantorCofactor f u v := rfl

theorem cantorReduce_snd (u v : R[X]) (c : R) :
    (cantorReduce f u v c).2 = (-v) %ₘ (C c * cantorCofactor f u v) := rfl

section ComposeAPI

variable {u₁ v₁ u₂ v₂ s₁ s₂ s₃ : R[X]}

theorem cantorCompose_monic (hu₁ : u₁.Monic) (hu₂ : u₂.Monic) :
    (cantorCompose f u₁ v₁ u₂ v₂ s₁ s₂ s₃).1.Monic := hu₁.mul hu₂

theorem cantorCompose_natDegree (hu₁ : u₁.Monic) (hu₂ : u₂.Monic) :
    (cantorCompose f u₁ v₁ u₂ v₂ s₁ s₂ s₃).1.natDegree = u₁.natDegree + u₂.natDegree :=
  hu₁.natDegree_mul hu₂

theorem cantorCompose_degree_lt [Nontrivial R] (hu₁ : u₁.Monic) (hu₂ : u₂.Monic) :
    (cantorCompose f u₁ v₁ u₂ v₂ s₁ s₂ s₃).2.degree
      < (cantorCompose f u₁ v₁ u₂ v₂ s₁ s₂ s₃).1.degree :=
  degree_modByMonic_lt _ (hu₁.mul hu₂)

/-- The composed datum lies on the curve. -/
theorem cantorCompose_dvd (hbez : s₁ * u₁ + s₂ * u₂ + s₃ * (v₁ + v₂) = 1)
    (hd₁ : u₁ ∣ v₁ ^ 2 - f) (hd₂ : u₂ ∣ v₂ ^ 2 - f) :
    (cantorCompose f u₁ v₁ u₂ v₂ s₁ s₂ s₃).1
      ∣ (cantorCompose f u₁ v₁ u₂ v₂ s₁ s₂ s₃).2 ^ 2 - f := by
  obtain ⟨w₁, hw₁⟩ := hd₁
  obtain ⟨w₂, hw₂⟩ := hd₂
  have hV : u₁ * u₂ ∣ cantorV f u₁ v₁ u₂ v₂ s₁ s₂ s₃ ^ 2 - f :=
    ⟨_, cantorV_sq_sub f hbez hw₁ hw₂⟩
  exact dvd_modByMonic_sq_sub_of_dvd f hV

end ComposeAPI

section ReduceAPI

variable {u v : R[X]} {c : R}

theorem cantorReduce_monic (hc : c * (cantorCofactor f u v).leadingCoeff = 1) :
    (cantorReduce f u v c).1.Monic :=
  monic_C_mul_of_mul_leadingCoeff_eq_one hc

theorem cantorReduce_degree_lt [Nontrivial R]
    (hc : c * (cantorCofactor f u v).leadingCoeff = 1) :
    (cantorReduce f u v c).2.degree < (cantorReduce f u v c).1.degree :=
  degree_modByMonic_lt _ (monic_C_mul_of_mul_leadingCoeff_eq_one hc)

theorem cantorReduce_dvd (hu : u.Monic) (hdvd : u ∣ v ^ 2 - f)
    (hc : c * (cantorCofactor f u v).leadingCoeff = 1) :
    (cantorReduce f u v c).1 ∣ (cantorReduce f u v c).2 ^ 2 - f :=
  C_mul_cofactor_dvd f (cantorCofactor_spec f hu hdvd) hc

theorem cantorReduce_natDegree (hu : u.Monic)
    (hc : c * (cantorCofactor f u v).leadingCoeff = 1) (hdvd : u ∣ v ^ 2 - f) :
    u.natDegree + (cantorReduce f u v c).1.natDegree = (v ^ 2 - f).natDegree := by
  rw [cantorReduce_fst, natDegree_C_mul_cofactor hc]
  exact natDegree_add_natDegree_cofactor f hu hc (cantorCofactor_spec f hu hdvd)

/-- A full-degree reduction step lands exactly at the generic degree
`max (2·(deg u - 1)) (deg f) - deg u`. -/
theorem natDegree_cantorReduce_of_fullDeg (hc : c * (cantorCofactor f u v).leadingCoeff = 1)
    (hfull : (cantorCofactor f u v).natDegree
      = max (2 * (u.natDegree - 1)) f.natDegree - u.natDegree) :
    (cantorReduce f u v c).1.natDegree = max (2 * (u.natDegree - 1)) f.natDegree - u.natDegree := by
  rw [cantorReduce_fst, natDegree_C_mul_cofactor hc, hfull]

end ReduceAPI

end Pipeline

section ClassLevel

open nonZeroDivisors

variable {K : Type*} [Field K] (f : K[X]) [NeZero (2 : K)] [Fact (Odd f.natDegree)]
  [Fact (Squarefree f)]

/-- **Composition computes the product class.** -/
theorem mk0_cantorCompose {u₁ v₁ u₂ v₂ s₁ s₂ s₃ : K[X]} (hu₁ : u₁.Monic) (hu₂ : u₂.Monic)
    (hbez : s₁ * u₁ + s₂ * u₂ + s₃ * (v₁ + v₂) = 1)
    (hd₁ : u₁ ∣ v₁ ^ 2 - f) (hd₂ : u₂ ∣ v₂ ^ 2 - f) :
    ClassGroup.mk0 ⟨mumfordIdeal f (cantorCompose f u₁ v₁ u₂ v₂ s₁ s₂ s₃).1
        (cantorCompose f u₁ v₁ u₂ v₂ s₁ s₂ s₃).2,
        mumfordIdeal_mem_nonZeroDivisors f (hu₁.mul hu₂).ne_zero _⟩
      = ClassGroup.mk0 ⟨mumfordIdeal f u₁ v₁,
            mumfordIdeal_mem_nonZeroDivisors f hu₁.ne_zero v₁⟩
        * ClassGroup.mk0 ⟨mumfordIdeal f u₂ v₂,
            mumfordIdeal_mem_nonZeroDivisors f hu₂.ne_zero v₂⟩ :=
  (congrArg ClassGroup.mk0 (Subtype.ext
    (mumfordIdeal_modByMonic f (u₁ * u₂) (cantorV f u₁ v₁ u₂ v₂ s₁ s₂ s₃)))).trans
    (mk0_mumfordIdeal_mul_of_bezout f hbez hd₁ hd₂ hu₁.ne_zero hu₂.ne_zero).symm

/-- **The reduction step preserves the class.** -/
theorem mk0_cantorReduce {u v : K[X]} {c : K} (hu : u.Monic) (hdvd : u ∣ v ^ 2 - f)
    (hc : c * (cantorCofactor f u v).leadingCoeff = 1) :
    ClassGroup.mk0 ⟨mumfordIdeal f u v, mumfordIdeal_mem_nonZeroDivisors f hu.ne_zero v⟩
      = ClassGroup.mk0 ⟨mumfordIdeal f (cantorReduce f u v c).1 (cantorReduce f u v c).2,
          mumfordIdeal_mem_nonZeroDivisors f (cantorReduce_monic f hc).ne_zero _⟩ := by
  have hw0 : cantorCofactor f u v ≠ 0 :=
    leadingCoeff_ne_zero.mp (right_ne_zero_of_mul_eq_one hc)
  exact mk0_mumfordIdeal_eq_mk0_cofactor_datum f hu.ne_zero hw0 hc
    (cantorCofactor_spec f hu hdvd)

end ClassLevel

section Chain

variable {R : Type*} [CommRing R] {f : R[X]}

/-- **Every stage of the four-stage pipeline is a Mumford datum**: compose, reduce, compose,
reduce carries monicity and the divisibility `u ∣ v² - f` through, given the two Bézout
certificates and the two reduction certificates. The stages are passed as equations, so a
caller can name them and reuse the invariants at each stage. -/
theorem cantorPipeline_stage_invariants {A₁ B₁ A₂ B₂ A₃ B₃ : R[X]}
    {s₁ s₂ s₃ t₁ t₂ t₃ : R[X]} {c₁ c₂ : R} {D₁ D₂ D₃ D₄ : R[X] × R[X]}
    (hD₁ : D₁ = cantorCompose f A₁ B₁ A₂ B₂ s₁ s₂ s₃)
    (hD₂ : D₂ = cantorReduce f D₁.1 D₁.2 c₁)
    (hD₃ : D₃ = cantorCompose f D₂.1 D₂.2 A₃ B₃ t₁ t₂ t₃)
    (hD₄ : D₄ = cantorReduce f D₃.1 D₃.2 c₂)
    (hA₁ : A₁.Monic) (hdA₁ : A₁ ∣ B₁ ^ 2 - f) (hA₂ : A₂.Monic) (hdA₂ : A₂ ∣ B₂ ^ 2 - f)
    (hA₃ : A₃.Monic) (hdA₃ : A₃ ∣ B₃ ^ 2 - f)
    (hbez₁ : s₁ * A₁ + s₂ * A₂ + s₃ * (B₁ + B₂) = 1)
    (hc₁ : c₁ * (cantorCofactor f D₁.1 D₁.2).leadingCoeff = 1)
    (hbez₂ : t₁ * D₂.1 + t₂ * A₃ + t₃ * (D₂.2 + B₃) = 1)
    (hc₂ : c₂ * (cantorCofactor f D₃.1 D₃.2).leadingCoeff = 1) :
    (D₁.1.Monic ∧ D₁.1 ∣ D₁.2 ^ 2 - f) ∧ (D₂.1.Monic ∧ D₂.1 ∣ D₂.2 ^ 2 - f)
      ∧ (D₃.1.Monic ∧ D₃.1 ∣ D₃.2 ^ 2 - f) ∧ (D₄.1.Monic ∧ D₄.1 ∣ D₄.2 ^ 2 - f) := by
  have h₁ : D₁.1.Monic ∧ D₁.1 ∣ D₁.2 ^ 2 - f :=
    ⟨hD₁ ▸ cantorCompose_monic f hA₁ hA₂, hD₁ ▸ cantorCompose_dvd f hbez₁ hdA₁ hdA₂⟩
  have h₂ : D₂.1.Monic ∧ D₂.1 ∣ D₂.2 ^ 2 - f :=
    ⟨hD₂ ▸ cantorReduce_monic f hc₁, hD₂ ▸ cantorReduce_dvd f h₁.1 h₁.2 hc₁⟩
  have h₃ : D₃.1.Monic ∧ D₃.1 ∣ D₃.2 ^ 2 - f :=
    ⟨hD₃ ▸ cantorCompose_monic f h₂.1 hA₃, hD₃ ▸ cantorCompose_dvd f hbez₂ h₂.2 hdA₃⟩
  exact ⟨h₁, h₂, h₃, hD₄ ▸ cantorReduce_monic f hc₂,
    hD₄ ▸ cantorReduce_dvd f h₃.1 h₃.2 hc₂⟩

end Chain

section MapPipeline

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : Polynomial R)

/-- A Mumford datum stays a Mumford datum under any base change. -/
theorem map_dvd_sq_sub {f u v : R[X]} (h : u ∣ v ^ 2 - f) :
    u.map φ ∣ (v.map φ) ^ 2 - f.map φ := by
  simpa only [Polynomial.map_sub, Polynomial.map_pow] using Polynomial.map_dvd φ h

/-- A Jacobian-unit Bézout certificate stays one under any base change. -/
theorem map_bezout {c u s v : R[X]} (h : c * u + s * (2 * v) = 1) :
    c.map φ * u.map φ + s.map φ * (2 * v.map φ) = 1 := by
  simpa using congrArg (Polynomial.map φ) h

/-- A three-term composition Bézout certificate stays one under any base change. -/
theorem map_bezout₃ {s₁ s₂ s₃ u₁ u₂ v₁ v₂ : R[X]}
    (h : s₁ * u₁ + s₂ * u₂ + s₃ * (v₁ + v₂) = 1) :
    s₁.map φ * u₁.map φ + s₂.map φ * u₂.map φ + s₃.map φ * (v₁.map φ + v₂.map φ) = 1 := by
  simpa using congrArg (Polynomial.map φ) h

theorem map_cantorV (u₁ v₁ u₂ v₂ s₁ s₂ s₃ : Polynomial R) :
    (cantorV f u₁ v₁ u₂ v₂ s₁ s₂ s₃).map φ
      = cantorV (f.map φ) (u₁.map φ) (v₁.map φ) (u₂.map φ) (v₂.map φ) (s₁.map φ)
        (s₂.map φ) (s₃.map φ) := by
  simp only [cantorV, Polynomial.map_add, Polynomial.map_mul]

theorem map_cantorCofactor {u : Polynomial R} (hu : u.Monic) (v : Polynomial R) :
    (cantorCofactor f u v).map φ = cantorCofactor (f.map φ) (u.map φ) (v.map φ) := by
  rw [cantorCofactor, cantorCofactor, map_divByMonic φ hu, Polynomial.map_sub,
    Polynomial.map_pow]

/-- The cofactor of a certified curve relation is the given cofactor. -/
theorem cantorCofactor_eq_of_sq_sub {f u v w : R[X]} (hu : u.Monic)
    (hw : v ^ 2 - f = u * w) : cantorCofactor f u v = w := by
  rw [cantorCofactor, hw, mul_divByMonic_cancel_left _ hu]

theorem map_cantorCompose {u₁ u₂ : Polynomial R} (hu₁ : u₁.Monic) (hu₂ : u₂.Monic)
    (v₁ v₂ s₁ s₂ s₃ : Polynomial R) :
    ((cantorCompose f u₁ v₁ u₂ v₂ s₁ s₂ s₃).1.map φ,
        (cantorCompose f u₁ v₁ u₂ v₂ s₁ s₂ s₃).2.map φ)
      = cantorCompose (f.map φ) (u₁.map φ) (v₁.map φ) (u₂.map φ) (v₂.map φ) (s₁.map φ)
        (s₂.map φ) (s₃.map φ) := by
  refine Prod.ext (by rw [cantorCompose_fst, cantorCompose_fst, Polynomial.map_mul]) ?_
  rw [cantorCompose_snd, cantorCompose_snd, map_modByMonic φ (hu₁.mul hu₂), map_cantorV,
    Polynomial.map_mul]

theorem map_cantorReduce {u v : Polynomial R} (hu : u.Monic) {c : R}
    (hc : c * (cantorCofactor f u v).leadingCoeff = 1) :
    ((cantorReduce f u v c).1.map φ, (cantorReduce f u v c).2.map φ)
      = cantorReduce (f.map φ) (u.map φ) (v.map φ) (φ c) := by
  have hCcw : (C c * cantorCofactor f u v).Monic := monic_C_mul_of_mul_leadingCoeff_eq_one hc
  have h1 : (cantorReduce f u v c).1.map φ
      = C (φ c) * cantorCofactor (f.map φ) (u.map φ) (v.map φ) := by
    rw [cantorReduce_fst, Polynomial.map_mul, map_C, map_cantorCofactor φ f hu]
  refine Prod.ext h1 ?_
  rw [cantorReduce_snd, cantorReduce_snd, map_modByMonic φ hCcw, Polynomial.map_neg,
    Polynomial.map_mul, map_C, map_cantorCofactor φ f hu]

/-- A reduction certificate remains one after base change along any ring homomorphism (into
a nontrivial ring): the leading coefficient stays invertible, hence survives. -/
theorem map_reduceCert [Nontrivial S] {u v : Polynomial R} {c : R} (hu : u.Monic)
    (hc : c * (cantorCofactor f u v).leadingCoeff = 1) :
    φ c * (cantorCofactor (f.map φ) (u.map φ) (v.map φ)).leadingCoeff = 1 := by
  have hφc : φ c * φ (cantorCofactor f u v).leadingCoeff = 1 := by rw [← map_mul, hc, map_one]
  rw [← map_cantorCofactor φ f hu,
    leadingCoeff_map_of_leadingCoeff_ne_zero φ (right_ne_zero_of_mul_eq_one hφc)]
  exact hφc

end MapPipeline

section CertLift

variable {R A : Type*} [CommRing R] [CommRing A] {φ : R →+* A}

/-- **Certificate lifting**: if `φ`-nonvanishing detects units in `R` (as for the residue map
of a local ring), then a reduction certificate over the image ring whose cofactor attains the
generic degree bound `max (2·(deg u - 1)) (deg f) - deg u` lifts to a certificate over `R`
mapping onto it. The degree condition squeezes the `R`-level cofactor degree against its
generic bound, so the leading coefficients correspond and are units. -/
theorem exists_reduceCert_map [Nontrivial A] (hdet : ∀ x : R, φ x ≠ 0 → IsUnit x)
    {f : R[X]} (hf : f.Monic) {u v : R[X]} {c' : A} (hu : u.Monic)
    (hv : v.degree < u.degree) (hdvd : u ∣ v ^ 2 - f)
    (hc' : c' * (cantorCofactor (f.map φ) (u.map φ) (v.map φ)).leadingCoeff = 1)
    (hfull : (cantorCofactor (f.map φ) (u.map φ) (v.map φ)).natDegree
      = max (2 * ((u.map φ).natDegree - 1)) (f.map φ).natDegree - (u.map φ).natDegree) :
    ∃ c : R, φ c = c' ∧ c * (cantorCofactor f u v).leadingCoeff = 1 := by
  have := φ.domain_nontrivial
  set w := cantorCofactor f u v
  have hwmap : w.map φ = cantorCofactor (f.map φ) (u.map φ) (v.map φ) :=
    map_cantorCofactor φ f hu v
  have hlcbar : (cantorCofactor (f.map φ) (u.map φ) (v.map φ)).leadingCoeff ≠ 0 :=
    right_ne_zero_of_mul_eq_one hc'
  have hw0 : w ≠ 0 := fun h0 ↦
    hlcbar (by rw [← hwmap, h0, Polynomial.map_zero, leadingCoeff_zero])
  -- degree bookkeeping: the `R`-level cofactor degree meets its generic bound
  have hnd : u.natDegree + w.natDegree = (v ^ 2 - f).natDegree := by
    rw [cantorCofactor_spec f hu hdvd, natDegree_mul' (by
      rw [hu.leadingCoeff, one_mul]; exact leadingCoeff_ne_zero.mpr hw0)]
  have hvle : v.natDegree ≤ u.natDegree - 1 := by
    rcases eq_or_ne v 0 with rfl | hv0
    · simp
    · have := natDegree_lt_natDegree hv0 hv
      lia
  have hbound : (v ^ 2 - f).natDegree ≤ max (2 * (u.natDegree - 1)) f.natDegree :=
    (natDegree_sub_le _ _).trans
      (max_le_max (natDegree_pow_le.trans (by lia)) le_rfl)
  -- squeeze against the attained bound on the image side
  have hle : (cantorCofactor (f.map φ) (u.map φ) (v.map φ)).natDegree ≤ w.natDegree :=
    hwmap ▸ natDegree_map_le
  rw [hu.natDegree_map, hf.natDegree_map] at hfull
  have hweq : w.natDegree
      = (cantorCofactor (f.map φ) (u.map φ) (v.map φ)).natDegree := by lia
  have hndmap : (w.map φ).natDegree = w.natDegree := by rw [hwmap, ← hweq]
  have hlc : (cantorCofactor (f.map φ) (u.map φ) (v.map φ)).leadingCoeff
      = φ w.leadingCoeff := by
    rw [← hwmap, leadingCoeff, leadingCoeff, hndmap, coeff_map]
  -- the leading coefficient is a unit; its inverse is the certificate
  obtain ⟨cu, hcu⟩ := hdet w.leadingCoeff (by rw [← hlc]; exact hlcbar)
  have hcc : (↑cu⁻¹ : R) * w.leadingCoeff = 1 := by rw [← hcu]; exact cu.inv_mul
  refine ⟨↑cu⁻¹, ?_, hcc⟩
  have h1 : φ ↑cu⁻¹ * (cantorCofactor (f.map φ) (u.map φ) (v.map φ)).leadingCoeff = 1 := by
    rw [hlc, ← map_mul, hcc, map_one]
  linear_combination c' * h1 - φ (↑cu⁻¹ : R) * hc'

end CertLift

section PipelineClass

open nonZeroDivisors

variable {K : Type*} [Field K] (f : K[X]) [NeZero (2 : K)] [Fact (Odd f.natDegree)]
  [Fact (Squarefree f)]

/-- `τ + (⊖τ)` is trivial in the class group. -/
theorem mk0_mumfordIdeal_mul_neg {u v : K[X]} (hu : u.Monic) (hdvd : u ∣ v ^ 2 - f) :
    ClassGroup.mk0 ⟨mumfordIdeal f u v, mumfordIdeal_mem_nonZeroDivisors f hu.ne_zero v⟩
      * ClassGroup.mk0 ⟨mumfordIdeal f u (-v),
          mumfordIdeal_mem_nonZeroDivisors f hu.ne_zero (-v)⟩ = 1 := by
  have hsf : Squarefree f := Fact.out
  have h2 : (2 : K) ≠ 0 := NeZero.ne 2
  have hprod : mumfordIdeal f u v * mumfordIdeal f u (-v)
      = Ideal.span {algebraMap K[X] (HypRing K f) u} := by
    rw [← map_star_mumfordIdeal f u v]
    exact mumfordIdeal_mul_map_star f hsf h2 hdvd
  rw [← map_mul]
  refine (ClassGroup.mk0_eq_one_iff _).mpr ?_
  change (mumfordIdeal f u v * mumfordIdeal f u (-v)).IsPrincipal
  rw [hprod]
  exact ⟨⟨_, rfl⟩⟩

/-- **The class of the four-stage pipeline**: composing two data, reducing, composing with
`⊖(u,v)` and reducing computes `c₁ + c₂ - τ` in the class group. -/
theorem mk0_cantorPipeline {U₁ V₁ U₂ V₂ u v s₁ s₂ s₃ t₁ t₂ t₃ : K[X]} {c₁ c₂ : K}
    {D₁ D₂ D₃ D₄ : K[X] × K[X]}
    (hD₁ : D₁ = cantorCompose f U₁ V₁ U₂ V₂ s₁ s₂ s₃)
    (hD₂ : D₂ = cantorReduce f D₁.1 D₁.2 c₁)
    (hD₃ : D₃ = cantorCompose f D₂.1 D₂.2 u (-v) t₁ t₂ t₃)
    (hD₄ : D₄ = cantorReduce f D₃.1 D₃.2 c₂)
    (hU₁ : U₁.Monic) (hdU₁ : U₁ ∣ V₁ ^ 2 - f) (hU₂ : U₂.Monic) (hdU₂ : U₂ ∣ V₂ ^ 2 - f)
    (hu : u.Monic) (hdu : u ∣ v ^ 2 - f)
    (hbez₁ : s₁ * U₁ + s₂ * U₂ + s₃ * (V₁ + V₂) = 1)
    (hc₁ : c₁ * (cantorCofactor f D₁.1 D₁.2).leadingCoeff = 1)
    (hbez₂ : t₁ * D₂.1 + t₂ * u + t₃ * (D₂.2 + -v) = 1)
    (hc₂ : c₂ * (cantorCofactor f D₃.1 D₃.2).leadingCoeff = 1)
    (h4m : D₄.1.Monic) :
    ClassGroup.mk0 ⟨mumfordIdeal f D₄.1 D₄.2,
        mumfordIdeal_mem_nonZeroDivisors f h4m.ne_zero _⟩
      = ClassGroup.mk0 ⟨mumfordIdeal f U₁ V₁,
            mumfordIdeal_mem_nonZeroDivisors f hU₁.ne_zero V₁⟩
        * ClassGroup.mk0 ⟨mumfordIdeal f U₂ V₂,
            mumfordIdeal_mem_nonZeroDivisors f hU₂.ne_zero V₂⟩
        * ClassGroup.mk0 ⟨mumfordIdeal f u (-v),
            mumfordIdeal_mem_nonZeroDivisors f hu.ne_zero (-v)⟩ := by
  have hdneg : u ∣ (-v) ^ 2 - f := by rwa [neg_pow_two]
  obtain ⟨⟨h1m, h1d⟩, h2, ⟨h3m, h3d⟩, -⟩ := cantorPipeline_stage_invariants hD₁ hD₂ hD₃ hD₄
    hU₁ hdU₁ hU₂ hdU₂ hu hdneg hbez₁ hc₁ hbez₂ hc₂
  have e4 : mumfordIdeal f D₄.1 D₄.2
      = mumfordIdeal f (cantorReduce f D₃.1 D₃.2 c₂).1 (cantorReduce f D₃.1 D₃.2 c₂).2 := by
    rw [hD₄]
  have e3 : mumfordIdeal f D₃.1 D₃.2
      = mumfordIdeal f (cantorCompose f D₂.1 D₂.2 u (-v) t₁ t₂ t₃).1
          (cantorCompose f D₂.1 D₂.2 u (-v) t₁ t₂ t₃).2 := by rw [hD₃]
  have e2 : mumfordIdeal f D₂.1 D₂.2
      = mumfordIdeal f (cantorReduce f D₁.1 D₁.2 c₁).1 (cantorReduce f D₁.1 D₁.2 c₁).2 := by
    rw [hD₂]
  have e1 : mumfordIdeal f D₁.1 D₁.2
      = mumfordIdeal f (cantorCompose f U₁ V₁ U₂ V₂ s₁ s₂ s₃).1
          (cantorCompose f U₁ V₁ U₂ V₂ s₁ s₂ s₃).2 := by rw [hD₁]
  have hmk2 : ClassGroup.mk0 ⟨mumfordIdeal f D₂.1 D₂.2,
      mumfordIdeal_mem_nonZeroDivisors f h2.1.ne_zero _⟩
      = ClassGroup.mk0 ⟨mumfordIdeal f (cantorReduce f D₁.1 D₁.2 c₁).1
          (cantorReduce f D₁.1 D₁.2 c₁).2, mumfordIdeal_mem_nonZeroDivisors f
            (cantorReduce_monic f hc₁).ne_zero _⟩ :=
    congrArg ClassGroup.mk0 (Subtype.ext e2)
  have hmk1 : ClassGroup.mk0 ⟨mumfordIdeal f D₁.1 D₁.2,
      mumfordIdeal_mem_nonZeroDivisors f h1m.ne_zero _⟩
      = ClassGroup.mk0 ⟨mumfordIdeal f (cantorCompose f U₁ V₁ U₂ V₂ s₁ s₂ s₃).1
          (cantorCompose f U₁ V₁ U₂ V₂ s₁ s₂ s₃).2, mumfordIdeal_mem_nonZeroDivisors f
            (cantorCompose_monic f hU₁ hU₂).ne_zero _⟩ :=
    congrArg ClassGroup.mk0 (Subtype.ext e1)
  calc ClassGroup.mk0 ⟨mumfordIdeal f D₄.1 D₄.2, _⟩
      = ClassGroup.mk0 ⟨mumfordIdeal f (cantorReduce f D₃.1 D₃.2 c₂).1
          (cantorReduce f D₃.1 D₃.2 c₂).2, mumfordIdeal_mem_nonZeroDivisors f
            (cantorReduce_monic f hc₂).ne_zero _⟩ :=
        congrArg ClassGroup.mk0 (Subtype.ext e4)
    _ = ClassGroup.mk0 ⟨mumfordIdeal f D₃.1 D₃.2,
          mumfordIdeal_mem_nonZeroDivisors f h3m.ne_zero _⟩ :=
        (mk0_cantorReduce f h3m h3d hc₂).symm
    _ = ClassGroup.mk0 ⟨mumfordIdeal f (cantorCompose f D₂.1 D₂.2 u (-v) t₁ t₂ t₃).1
          (cantorCompose f D₂.1 D₂.2 u (-v) t₁ t₂ t₃).2, mumfordIdeal_mem_nonZeroDivisors
            f (cantorCompose_monic f h2.1 hu).ne_zero _⟩ :=
        congrArg ClassGroup.mk0 (Subtype.ext e3)
    _ = ClassGroup.mk0 ⟨mumfordIdeal f D₂.1 D₂.2,
            mumfordIdeal_mem_nonZeroDivisors f h2.1.ne_zero _⟩
        * ClassGroup.mk0 ⟨mumfordIdeal f u (-v),
            mumfordIdeal_mem_nonZeroDivisors f hu.ne_zero _⟩ :=
        mk0_cantorCompose f h2.1 hu hbez₂ h2.2 hdneg
    _ = ClassGroup.mk0 ⟨mumfordIdeal f (cantorReduce f D₁.1 D₁.2 c₁).1
          (cantorReduce f D₁.1 D₁.2 c₁).2, mumfordIdeal_mem_nonZeroDivisors f
            (cantorReduce_monic f hc₁).ne_zero _⟩
        * ClassGroup.mk0 ⟨mumfordIdeal f u (-v),
            mumfordIdeal_mem_nonZeroDivisors f hu.ne_zero _⟩ := by rw [hmk2]
    _ = ClassGroup.mk0 ⟨mumfordIdeal f D₁.1 D₁.2,
            mumfordIdeal_mem_nonZeroDivisors f h1m.ne_zero _⟩
        * ClassGroup.mk0 ⟨mumfordIdeal f u (-v),
            mumfordIdeal_mem_nonZeroDivisors f hu.ne_zero _⟩ := by
        rw [← mk0_cantorReduce f h1m h1d hc₁]
    _ = ClassGroup.mk0 ⟨mumfordIdeal f (cantorCompose f U₁ V₁ U₂ V₂ s₁ s₂ s₃).1
          (cantorCompose f U₁ V₁ U₂ V₂ s₁ s₂ s₃).2, mumfordIdeal_mem_nonZeroDivisors f
            (cantorCompose_monic f hU₁ hU₂).ne_zero _⟩
        * ClassGroup.mk0 ⟨mumfordIdeal f u (-v),
            mumfordIdeal_mem_nonZeroDivisors f hu.ne_zero _⟩ := by rw [hmk1]
    _ = ClassGroup.mk0 ⟨mumfordIdeal f U₁ V₁,
            mumfordIdeal_mem_nonZeroDivisors f hU₁.ne_zero V₁⟩
        * ClassGroup.mk0 ⟨mumfordIdeal f U₂ V₂,
            mumfordIdeal_mem_nonZeroDivisors f hU₂.ne_zero V₂⟩
        * ClassGroup.mk0 ⟨mumfordIdeal f u (-v),
            mumfordIdeal_mem_nonZeroDivisors f hu.ne_zero _⟩ := by
        rw [mk0_cantorCompose f hU₁ hU₂ hbez₁ hdU₁ hdU₂]

end PipelineClass

end ChabautyColeman

end
