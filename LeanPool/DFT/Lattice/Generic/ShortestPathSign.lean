/-
Copyright (c) 2026 Miguel A. L. Marques, Stefano Pittalis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques, Stefano Pittalis
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.Generic.SignGauge
public import LeanPool.DFT.Lattice.Generic.DensityDim.Fermions
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Generic HK when all shortest paths between two sites have hopping products of one sign

The sign hypothesis `0 < s * t a b` of `generic_hk_lattice_fermions_w` enters its proof only in
`Lval_ne_zero`: at a large potential on the target site, every shortest path from the partner
site to the target contributes to the partner route sum with the sign of `(-1)^d` times its
hopping product (`d` the distance), the same for every shortest path, so the sum is nonzero. The
same argument works under the weaker hypothesis `ShortestPathSigned G t`:
for every site `b` there are signs `ε q = ±1` with `ε q * t q r * ε r > 0` whenever `q` and `r` are
adjacent and `r` is one step closer to `b`. The condition forces `t q r ≠ 0` on every edge
(`ShortestPathSigned.ne_zero`); for such hopping it says that, for any two sites, all shortest paths
between them have hopping products of the same sign. For symmetric hopping, each undirected edge
has a single sign, giving the distance-compatible signed graph interpretation of Shahul Hameed,
Shijin, Soorya, Germina and Zaslavsky (Linear Algebra Appl. 608, 236 (2021)). This interpretation
is informal.

* the same route-sum, resonant determinant and generic-potential lemmas handle both sign
  conditions;
* `hstar_lattice_fermions_shortest`, `generic_hk_lattice_fermions_shortest`,
  `exists_poly_lattice_fermions_shortest`, `dimH_nonUVDens_lattice_fermions_shortest` and its
  primed form;
* the class contains the hoppings of a common sign and their orbital sign changes
  (`shortestPathSigned_of_common_sign`, `shortestPathSigned_gaugeHop`,
  `shortestPathSigned_of_gauge`), and every nonzero hopping on a complete graph
  (`shortestPathSigned_top`); on the complete graph with four sites and one bond of the other
  sign it is strictly larger than the gauge class (`k4_shortestPathSigned_not_gauge`); if every
  edge joins two sites whose distances to some site differ by one, in particular on a connected
  bipartite graph, it is the gauge class (`common_sign_of_shortestPathSigned_layered`,
  `dist_ne_of_adj_of_isBipartite`, `common_sign_of_shortestPathSigned_bipartite`);
* it excludes the square with `t₀₁ t₁₂ t₂₃ t₃₀ < 0` (`not_shortestPathSigned_of_two_paths`,
  `square_not_shortestPathSigned`).
-/

@[expose] public section

namespace DFT

open Matrix Filter Topology MvPolynomial

variable {M N : ℕ}

/-- **(H*) for spinless lattice fermions** when the shortest paths between any two sites carry
hopping products of one sign (`ShortestPathSigned`). -/
theorem hstar_lattice_fermions_shortest {G : SimpleGraph (Fin M)} [DecidableRel G.Adj]
    (hG : G.Connected) {t : Fin M → Fin M → ℝ} (hsp : ShortestPathSigned G t) (c : Conf M N)
    (Vint : Conf M N → ℝ) :
    krylovPoly (H0Fw G t Vint) occF c (fun j => (Fintype.equivFin (Conf M N) j : ℕ)) ≠ 0 := by
  obtain ⟨u, hw, hα, -⟩ := exists_good_u_of_Lval hG
    (Lval_ne_zero_of_shortestPathSigned hG hsp) c
    (κ := Empty) (fun k => k.elim) (fun k => k.elim)
  exact hstar_of_alpha (lip_mopt hG t c) (mopt_self G c) occF u hw hα Vint

/-- **Generic Hohenberg–Kohn theorem when the shortest paths between any two sites carry hopping
products of one sign.**
On a connected graph with symmetric hopping, `0 < N < M` and any configuration-diagonal
interaction, under `ShortestPathSigned G t` the potentials with a non-uniquely v-representable
ground state lie in a closed, nowhere dense, null set. -/
theorem generic_hk_lattice_fermions_shortest {G : SimpleGraph (Fin M)} [DecidableRel G.Adj]
    (hG : G.Connected) {t : Fin M → Fin M → ℝ} (htsym : ∀ a b, t a b = t b a)
    (hsp : ShortestPathSigned G t) (hN0 : 0 < N) (hNM : N < M) (Vint : Conf M N → ℝ) :
    ∃ Z : Set (Fin M → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ MeasureTheory.volume Z = 0 ∧
      {v | NonUV (H0Fw G t Vint) occF v} ⊆ Z :=
  generic_hk_ae (H0Fw_isSymm G htsym Vint) (rigid_occF hN0 hNM) _
    (fun c => hstar_lattice_fermions_shortest hG hsp c Vint)

/-- A nonzero polynomial vanishing on the exceptional potentials, under `ShortestPathSigned`. -/
theorem exists_poly_lattice_fermions_shortest {G : SimpleGraph (Fin M)} [DecidableRel G.Adj]
    (hG : G.Connected) {t : Fin M → Fin M → ℝ} (htsym : ∀ a b, t a b = t b a)
    (hsp : ShortestPathSigned G t) (hN0 : 0 < N) (hNM : N < M) (Vint : Conf M N → ℝ) :
    ∃ P : MvPolynomial (Fin M) ℝ, P ≠ 0 ∧
      ∀ v, NonUV (H0Fw G t Vint) (occF : Fin M → Conf M N → ℝ) v → eval v P = 0 :=
  exists_krylov_certificate (Tr := constPot) (H0Fw_isSymm G htsym Vint) (rigid_occF hN0 hNM)
    (fun j => (Fintype.equivFin (Conf M N) j : ℕ))
    (fun c => hstar_lattice_fermions_shortest hG hsp c Vint)


/-- **Non-uv densities when the shortest paths between any two sites carry hopping products of one
sign**: Hausdorff dimension at most `M - 3`. -/
theorem dimH_nonUVDens_lattice_fermions_shortest {G : SimpleGraph (Fin M)} [DecidableRel G.Adj]
    (hG : G.Connected) {t : Fin M → Fin M → ℝ} (htsym : ∀ a b, t a b = t b a)
    (hsp : ShortestPathSigned G t) (hN0 : 0 < N) (hNM : N < M) (Vint : Conf M N → ℝ) :
    dimH (NonUVDens (H0Fw G t Vint) (occF : Fin M → Conf M N → ℝ)) ≤ (M : ENNReal) - 3 := by
  obtain ⟨P, hP, hPZ⟩ := exists_poly_lattice_fermions_shortest hG htsym hsp hN0 hNM Vint
  simpa using dimH_nonUVDens_le (H0Fw_isSymm G htsym Vint) ⟨N, sum_occF_eq⟩ hP hPZ

/-- `dimH_nonUVDens_lattice_fermions_shortest` in the form `dimH + 3 ≤ M` (when there are non-uv
densities at all). -/
theorem dimH_nonUVDens_lattice_fermions_shortest' {G : SimpleGraph (Fin M)} [DecidableRel G.Adj]
    (hG : G.Connected) {t : Fin M → Fin M → ℝ} (htsym : ∀ a b, t a b = t b a)
    (hsp : ShortestPathSigned G t) (hN0 : 0 < N) (hNM : N < M) (Vint : Conf M N → ℝ)
    (hne : (NonUVDens (H0Fw G t Vint) (occF : Fin M → Conf M N → ℝ)).Nonempty) :
    dimH (NonUVDens (H0Fw G t Vint) (occF : Fin M → Conf M N → ℝ)) + 3 ≤ M := by
  obtain ⟨P, hP, hPZ⟩ := exists_poly_lattice_fermions_shortest hG htsym hsp hN0 hNM Vint
  simpa using dimH_nonUVDens (H0Fw_isSymm G htsym Vint) ⟨N, sum_occF_eq⟩ hP hPZ hne

/-! ### The class -/

/-- Orbital sign changes preserve `ShortestPathSigned` (`ε ↦ σ ε`). -/
theorem shortestPathSigned_gaugeHop {G : SimpleGraph (Fin M)} {σ : Fin M → ℝ}
    (hσ : ∀ i, σ i * σ i = 1) {t : Fin M → Fin M → ℝ} (h : ShortestPathSigned G t) :
    ShortestPathSigned G (gaugeHop σ t) := by
  intro b
  obtain ⟨ε, hε, hl⟩ := h b
  refine ⟨fun q => σ q * ε q, fun q => by linear_combination (ε q * ε q) * hσ q + hε q,
    fun q r hqr hd => ?_⟩
  have e : σ q * ε q * gaugeHop σ t q r * (σ r * ε r) =
      (σ q * σ q) * (σ r * σ r) * (ε q * t q r * ε r) := by simp only [gaugeHop]; ring
  simp only
  rw [e, hσ q, hσ r, one_mul, one_mul]
  exact hl q r hqr hd

/-- **The gauge class is contained in `ShortestPathSigned`**: hopping that orbital sign changes
bring to a common sign is `ShortestPathSigned`. -/
theorem shortestPathSigned_of_gauge {G : SimpleGraph (Fin M)} {t : Fin M → Fin M → ℝ}
    {σ : Fin M → ℝ} (hσ : ∀ i, σ i * σ i = 1) {s : ℝ}
    (hts : ∀ a b, G.Adj a b → 0 < s * (σ a * σ b * t a b)) : ShortestPathSigned G t := by
  have h := shortestPathSigned_gaugeHop hσ
    (shortestPathSigned_of_common_sign (t := gaugeHop σ t) (fun a b hab => hts a b hab))
  rwa [gaugeHop_gaugeHop hσ] at h

/-- On a complete graph every nonzero hopping pattern qualifies: the only shortest path from `q`
to `b` is the bond `q b` (`ε b = 1`, `ε q = sign t q b`). -/
theorem shortestPathSigned_top {t : Fin M → Fin M → ℝ} (ht : ∀ a b, a ≠ b → t a b ≠ 0) :
    ShortestPathSigned (⊤ : SimpleGraph (Fin M)) t := by
  intro b
  refine ⟨fun q => if q = b then 1 else (if 0 < t q b then 1 else -1),
    fun q => by dsimp only; split_ifs <;> norm_num, fun q r hqr hd => ?_⟩
  have hqr' : q ≠ r := hqr
  have hrb : r = b := by
    by_contra hrb
    rw [SimpleGraph.dist_top_of_ne (Ne.symm hrb)] at hd
    have hq : (⊤ : SimpleGraph (Fin M)).dist b q ≤ 1 := by
      rw [SimpleGraph.dist_top]; split_ifs <;> simp
    omega
  subst hrb
  have h0 := ht q r hqr'
  simp only [hqr', ↓reduceIte]
  split_ifs with h
  · simpa using h
  · push Not at h
    have : t q r < 0 := lt_of_le_of_ne h h0
    linarith

/-- **`ShortestPathSigned` is strictly larger than the gauge class**: on the complete graph with
four sites, every nonzero hopping qualifies, but if `t₀₁ t₁₂ t₂₃ t₃₀ < 0` (e.g. one bond of the
other sign) no orbital sign changes bring it to a common sign. -/
theorem k4_shortestPathSigned_not_gauge {t : Fin 4 → Fin 4 → ℝ} (ht : ∀ a b, a ≠ b → t a b ≠ 0)
    (hneg : t 0 1 * t 1 2 * t 2 3 * t 3 0 < 0) :
    ShortestPathSigned (⊤ : SimpleGraph (Fin 4)) t ∧
      ¬ ∃ σ : Fin 4 → ℝ, ∃ s : ℝ, (∀ i, σ i * σ i = 1) ∧
        ∀ a b, (⊤ : SimpleGraph (Fin 4)).Adj a b → 0 < s * (σ a * σ b * t a b) := by
  refine ⟨shortestPathSigned_top ht, ?_⟩
  rintro ⟨σ, s, hσ, h⟩
  exact cycle4_no_common_sign hσ s t 0 1 2 3 hneg
    ⟨h 0 1 (by decide), h 1 2 (by decide), h 2 3 (by decide), h 3 0 (by decide)⟩

/-- **On a graph layered around a site the class is the gauge class**: if every edge joins two
sites whose distances to a site `b` differ (by one, necessarily), symmetric hopping with
`ShortestPathSigned` is brought to positive hopping by the orbital signs `σ = ε` of `b` (the
hypothesis of `generic_hk_lattice_fermions_gauge` with `s = 1`). Every connected bipartite graph is
layered around each of its sites (`dist_ne_of_adj_of_isBipartite`). -/
theorem common_sign_of_shortestPathSigned_layered {G : SimpleGraph (Fin M)} (hG : G.Connected)
    {t : Fin M → Fin M → ℝ} (htsym : ∀ a b, t a b = t b a) (hsp : ShortestPathSigned G t)
    (b : Fin M) (hlay : ∀ q r, G.Adj q r → G.dist b q ≠ G.dist b r) :
    ∃ σ : Fin M → ℝ, (∀ i, σ i * σ i = 1) ∧ ∀ q r, G.Adj q r → 0 < 1 * (σ q * σ r * t q r) := by
  obtain ⟨ε, hε, hl⟩ := hsp b
  refine ⟨ε, hε, fun q r hqr => ?_⟩
  have h1 : G.dist b q ≤ G.dist b r + 1 := by
    have := hG.dist_triangle (u := b) (v := r) (w := q)
    rwa [SimpleGraph.dist_eq_one_iff_adj.mpr hqr.symm] at this
  have h2 : G.dist b r ≤ G.dist b q + 1 := by
    have := hG.dist_triangle (u := b) (v := q) (w := r)
    rwa [SimpleGraph.dist_eq_one_iff_adj.mpr hqr] at this
  have hne := hlay q r hqr
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := hl r q hqr.symm (by omega)
    rw [htsym r q] at this
    linarith [show ε r * t q r * ε q = 1 * (ε q * ε r * t q r) by ring]
  · have := hl q r hqr (by omega)
    linarith [show ε q * t q r * ε r = 1 * (ε q * ε r * t q r) by ring]

/-- On a connected bipartite graph every edge joins two sites at different distances from `b`. -/
theorem dist_ne_of_adj_of_isBipartite {V : Type*} {G : SimpleGraph V} (hG : G.Connected)
    (hbip : G.IsBipartite) (b : V) {q r : V} (hqr : G.Adj q r) : G.dist b q ≠ G.dist b r := by
  obtain ⟨c0⟩ := hbip
  let c : G.Coloring Bool := G.recolorOfEquiv finTwoEquiv c0
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist b q
  obtain ⟨p', hp'⟩ := hG.exists_walk_length_eq_dist b r
  have h1 := c.even_length_iff_congr p
  have h2 := c.even_length_iff_congr p'
  have hc : c q ≠ c r := c.valid hqr
  intro h
  rw [hp] at h1; rw [hp', ← h] at h2
  have : (c b = true ↔ c q = true) ↔ (c b = true ↔ c r = true) := h1.symm.trans h2
  cases hb : c b <;> cases hq : c q <;> cases hr : c r <;> simp_all

/-- **On a bipartite graph the class is the gauge class**: on a connected bipartite graph,
symmetric hopping with `ShortestPathSigned` is brought to positive hopping by orbital sign changes
(cf. Theorem 5.1 of Shahul Hameed et al., Linear Algebra Appl. 608, 236 (2021)). -/
theorem common_sign_of_shortestPathSigned_bipartite {G : SimpleGraph (Fin M)} (hG : G.Connected)
    (hbip : G.IsBipartite) {t : Fin M → Fin M → ℝ} (htsym : ∀ a b, t a b = t b a)
    (hsp : ShortestPathSigned G t) :
    ∃ σ : Fin M → ℝ, (∀ i, σ i * σ i = 1) ∧ ∀ q r, G.Adj q r → 0 < 1 * (σ q * σ r * t q r) := by
  obtain ⟨b⟩ := hG.nonempty
  exact common_sign_of_shortestPathSigned_layered hG htsym hsp b
    (fun q r hqr => dist_ne_of_adj_of_isBipartite hG hbip b hqr)

/-- Two shortest paths `q → r₁ → b` and `q → r₂ → b` (`q`, `b` at distance two) whose hopping
products have opposite signs exclude `ShortestPathSigned`. -/
theorem not_shortestPathSigned_of_two_paths {G : SimpleGraph (Fin M)} {t : Fin M → Fin M → ℝ}
    {b q r₁ r₂ : Fin M} (h1 : G.Adj q r₁) (h1b : G.Adj r₁ b) (h2 : G.Adj q r₂) (h2b : G.Adj r₂ b)
    (hbq : b ≠ q) (hnadj : ¬ G.Adj b q) (hneg : t q r₁ * t r₁ b * (t q r₂ * t r₂ b) < 0) :
    ¬ ShortestPathSigned G t := by
  intro hsp
  obtain ⟨ε, hε, hl⟩ := hsp b
  have d1 : G.dist b r₁ = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h1b.symm
  have d2 : G.dist b r₂ = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h2b.symm
  have d0 : G.dist b b = 0 := SimpleGraph.dist_self
  have hq : G.dist b q = 2 := by
    have hle : G.dist b q ≤ 2 :=
      SimpleGraph.dist_le (SimpleGraph.Walk.cons h1b.symm
        (SimpleGraph.Walk.cons h1.symm SimpleGraph.Walk.nil))
    have hne0 : G.dist b q ≠ 0 := by
      rw [Ne, SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable]
      push Not
      exact ⟨hbq, (h1b.symm.reachable).trans h1.symm.reachable⟩
    have hne1 : G.dist b q ≠ 1 := fun h => hnadj (SimpleGraph.dist_eq_one_iff_adj.mp h)
    omega
  have p1 := hl q r₁ h1 (by omega)
  have p2 := hl r₁ b h1b (by omega)
  have p3 := hl q r₂ h2 (by omega)
  have p4 := hl r₂ b h2b (by omega)
  have hp := mul_pos (mul_pos p1 p2) (mul_pos p3 p4)
  have e : ε q * t q r₁ * ε r₁ * (ε r₁ * t r₁ b * ε b) *
      (ε q * t q r₂ * ε r₂ * (ε r₂ * t r₂ b * ε b)) =
      (ε q * ε q) * (ε r₁ * ε r₁) * (ε r₂ * ε r₂) * (ε b * ε b) *
        (t q r₁ * t r₁ b * (t q r₂ * t r₂ b)) := by ring
  rw [e, hε, hε, hε, hε] at hp
  linarith

/-- **The square with one bond of the other sign is not in the class**: on a graph with the bonds
`0 1`, `1 2`, `2 3`, `3 0` and without the bond `0 2`, symmetric hopping with
`t₀₁ t₁₂ t₂₃ t₃₀ < 0` violates `ShortestPathSigned` (the paths `2 → 1 → 0` and `2 → 3 → 0`). -/
theorem square_not_shortestPathSigned {G : SimpleGraph (Fin 4)} {t : Fin 4 → Fin 4 → ℝ}
    (htsym : ∀ a b, t a b = t b a) (h01 : G.Adj 0 1) (h12 : G.Adj 1 2) (h23 : G.Adj 2 3)
    (h30 : G.Adj 3 0) (h02 : ¬ G.Adj 0 2) (hneg : t 0 1 * t 1 2 * t 2 3 * t 3 0 < 0) :
    ¬ ShortestPathSigned G t := by
  apply not_shortestPathSigned_of_two_paths (b := 0) (q := 2) (r₁ := 1) (r₂ := 3) h12.symm
    h01.symm h23 h30 (by decide) h02
  rw [htsym 2 1, htsym 1 0]
  linarith [hneg, show t 0 1 * t 1 2 * t 2 3 * t 3 0 = t 1 2 * t 0 1 * (t 2 3 * t 3 0) by ring]

end DFT
