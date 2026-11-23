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
between them have hopping products of the same sign (not formalized). In graph theory the signs of
`t` then form a distance-compatible signed graph (Shahul Hameed, Shijin, Soorya, Germina, Zaslavsky,
Linear Algebra Appl. 608, 236 (2021)).

* `ShortestPathSigned.ne_zero`; `Lval_ne_zero_of_shortestPathSigned`; `exists_DExp_ne_of_Lval`,
  `exists_good_u_of_Lval` (verbatim copies of `exists_DExp_ne`, `exists_good_u` with the conclusion
  of `Lval_ne_zero` as a hypothesis; to keep in sync with them);
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

/-- **All shortest paths between two sites have hopping products of one sign.** For every site `b`
there are signs `ε q = ±1` with `ε q * t q r * ε r > 0` whenever `q` and `r` are adjacent and `r` is
one step closer to `b` than `q`. (This forces `t q r ≠ 0` on every edge,
`ShortestPathSigned.ne_zero`.) -/
def ShortestPathSigned (G : SimpleGraph (Fin M)) (t : Fin M → Fin M → ℝ) : Prop :=
  ∀ b : Fin M, ∃ ε : Fin M → ℝ, (∀ q, ε q * ε q = 1) ∧
    ∀ q r, G.Adj q r → G.dist b r + 1 = G.dist b q → 0 < ε q * t q r * ε r

/-- `ShortestPathSigned` forces nonzero hopping on every edge (take `b = r`). -/
theorem ShortestPathSigned.ne_zero {G : SimpleGraph (Fin M)} {t : Fin M → Fin M → ℝ}
    (h : ShortestPathSigned G t) {q r : Fin M} (hqr : G.Adj q r) : t q r ≠ 0 := by
  obtain ⟨ε, -, hl⟩ := h r
  have hd : G.dist r r + 1 = G.dist r q := by
    rw [SimpleGraph.dist_self, SimpleGraph.dist_eq_one_iff_adj.mpr hqr.symm]
  intro h0
  have := hl q r hqr hd
  rw [h0] at this
  simp at this

/-- **The partner route sums do not vanish under `ShortestPathSigned`.** As `Lval_ne_zero`, with
the common sign of the hopping replaced by the signs `ε` that `ShortestPathSigned` gives for the
partner site `π`. -/
theorem Lval_ne_zero_of_shortestPathSigned {G : SimpleGraph (Fin M)} [DecidableRel G.Adj]
    (hG : G.Connected) {t : Fin M → Fin M → ℝ} (hsp : ShortestPathSigned G t)
    (us : Fin M → ℝ) (π a : Fin M) (hπa : π ≠ a) (hhigh : ∀ q, q ≠ a → q ≠ π → us q < us a) :
    Lval G t us π a π ≠ 0 := by
  obtain ⟨ε, hε, hlay⟩ := hsp π
  have hpos : ∀ n q, G.dist π q = n → n < G.dist π a →
      0 < (-1) ^ n * (ε π * ε q) * Λ G t us π a π n q := by
    intro n
    induction n with
    | zero =>
      intro q hq _
      have : q = π := (dist_eq_zero_iff hG).mp hq
      subst this; simp [Λ, hε]
    | succ n ih =>
      intro q hq hlt
      have hqπ : q ≠ π := by intro h; subst h; simp at hq
      have hqa : q ≠ a := by intro h; subst h; omega
      have hden : 0 < us a - us q := sub_pos.mpr (hhigh q hqa hqπ)
      have hrw : (-1) ^ (n + 1) * (ε π * ε q) * Λ G t us π a π (n + 1) q =
          (∑ r, (if G.Adj q r ∧ G.dist π r = n then
              (ε q * t q r * ε r) * ((-1) ^ n * (ε π * ε r) * Λ G t us π a π n r) else 0)) /
            (us a - us q) := by
        simp only [Λ, ite_eq_left hq, ite_eq_right hqπ]
        rw [mul_div_assoc', Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl; intro r _
        split_ifs
        · linear_combination (-(-1 : ℝ) ^ n * ε π * ε q * t q r * Λ G t us π a π n r) * hε r
        · simp
      rw [hrw]
      apply div_pos _ hden
      obtain ⟨r0, hr0, hdr0⟩ := exists_pred hG hq
      apply Finset.sum_pos' (fun r _ => by
        split_ifs with hr
        · exact (mul_pos (hlay q r hr.1 (by omega)) (ih r hr.2 (by omega))).le
        · exact le_refl 0)
      exact ⟨r0, Finset.mem_univ _, by
        rw [ite_eq_left ⟨hr0, hdr0⟩]
        exact mul_pos (hlay q r0 hr0 (by omega)) (ih r0 hdr0 (by omega))⟩
  have hda : 0 < G.dist π a := by
    by_contra h0; push Not at h0
    exact hπa ((dist_eq_zero_iff hG).mp (by omega)).symm
  obtain ⟨p0, hp0, hdp0⟩ :=
      exists_pred hG (n := G.dist π a - 1) (by omega : G.dist π a = G.dist π a - 1 + 1)
  intro h0
  have hsum : 0 < ∑ p, (if G.Adj a p ∧ G.dist π p + 1 = G.dist π a then
      (ε a * t a p * ε p) * ((-1) ^ (G.dist π p) * (ε π * ε p) *
        Λ G t us π a π (G.dist π p) p) else 0) := by
    apply Finset.sum_pos' (fun p _ => by
      split_ifs with hp
      · exact (mul_pos (hlay a p hp.1 hp.2) (hpos _ p rfl (by omega))).le
      · exact le_refl 0)
    exact ⟨p0, Finset.mem_univ _, by
      rw [ite_eq_left ⟨hp0, by omega⟩]
      exact mul_pos (hlay a p0 hp0 (by omega)) (hpos _ p0 rfl (by omega))⟩
  have : (-1) ^ (G.dist π a) * (ε π * ε a) * Lval G t us π a π =
      ∑ p, (if G.Adj a p ∧ G.dist π p + 1 = G.dist π a then
        (ε a * t a p * ε p) * ((-1) ^ (G.dist π p) * (ε π * ε p) *
          Λ G t us π a π (G.dist π p) p) else 0) := by
    unfold Lval
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _
    split_ifs with hp
    · rw [← hp.2]
      linear_combination (-(-1 : ℝ) ^ (G.dist π p) * ε π * ε a * t a p *
        Λ G t us π a π (G.dist π p) p) * hε p
    · simp
  rw [h0, mul_zero] at this
  exact hsum.ne' this.symm

/-- `exists_DExp_ne` (`ResonantPoint.lean`) with the conclusion of `Lval_ne_zero` (partner route
sums nonzero when the target is the highest site) as a hypothesis `hL`; otherwise a verbatim
copy. -/
theorem exists_DExp_ne_of_Lval {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    {t : Fin M → Fin M → ℝ}
    (hL : ∀ (us : Fin M → ℝ) (π a : Fin M), π ≠ a → (∀ q, q ≠ a → q ≠ π → us q < us a) →
      Lval G t us π a π ≠ 0) (c y : Conf M N) :
    ∃ u : Fin M → ℝ, Function.Injective u ∧ DExp G t u c y ≠ 0 := by
  classical
  obtain ⟨σ0, h0, hfix⟩ := exists_opt_fixing hG c y
  set R := rep c y σ0
  set ι := {l : Fin N // τs y l ∉ c.1}
  -- 1. a common point θ where all partner route sums are nonzero
  have hpt : ∀ l : ι, ∃ θ : Fin M → ℝ, Function.Injective θ ∧
      Lval G t (fun i => θ (R i)) (partner c σ0 l.1) (τs y l.1) (partner c σ0 l.1) ≠ 0 := by
    intro l
    set a := τs y l.1
    refine ⟨fun i => if i = a then (M : ℝ) else (i : ℝ), ?_, ?_⟩
    · intro i j hij
      simp only at hij
      split_ifs at hij with hi hj hj
      · rw [hi, hj]
      · exfalso; have := j.isLt; have : (M : ℝ) = (j : ℕ) := hij; norm_cast at this; omega
      · exfalso; have := i.isLt; have : ((i : ℕ) : ℝ) = M := hij; norm_cast at this; omega
      · exact Fin.ext (by exact_mod_cast hij)
    · have hπa : partner c σ0 l.1 ≠ a := fun h => l.2 (by
        have hm : partner c σ0 l.1 ∈ c.1 := τs_mem c _
        rw [h] at hm; exact hm)
      apply hL _ _ _ hπa
      intro q hqa hqπ
      have hRa : R a = a := rep_target c y σ0 hfix l.1
      have hRq : R q ≠ a := by
        intro h
        rcases rep_eq_target c y σ0 h with h1 | ⟨-, h1⟩
        · exact hqa h1
        · exact hqπ h1
      simp only [hRa, ite_eq_right hRq]
      exact_mod_cast (R q).isLt
  obtain ⟨θ, hθ, hθS, -⟩ := exists_common_ne (κ := Fin 0)
    (fun l : ι => fun θ => Lval G t (fun i => θ (R i)) (partner c σ0 l.1) (τs y l.1)
        (partner c σ0 l.1))
    (fun l => ratOn_Lval G t R _ _ _) hpt (fun k => k.elim0) (fun k => k.elim0)
  -- 2. the resonant point and the line
  set us : Fin M → ℝ := fun i => θ (R i)
  set δ : Fin M → ℝ := fun i => (i : ℝ)
  have hδinj : Function.Injective δ := fun i j h => by
    have h' : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := h
    exact Fin.ext (by exact_mod_cast h')
  have hRtarget : ∀ l, R (τs y l) = τs y l := rep_target c y σ0 hfix
  have hRp : ∀ l, τs y l ∉ c.1 → R (partner c σ0 l) = τs y l := fun l hl => rep_partner c y σ0 hl
  have hReq : ∀ {l : Fin N} {z : Fin M}, R z = τs y l →
      z = τs y l ∨ (τs y l ∉ c.1 ∧ z = partner c σ0 l) := fun h => rep_eq_target c y σ0 h
  have hev := DExp_eventually_ne hG t c y σ0 h0 hfix us δ
    (fun l hl => by
      change θ (R (τs y l)) = θ (R (partner c σ0 l))
      rw [hRtarget, hRp l hl])
    (fun l hl z hz => by
      simp only [us, hRtarget] at hz
      rcases hReq (hθ hz) with h1 | ⟨-, h1⟩
      · exact Or.inl h1
      · exact Or.inr h1)
    (fun l hl z hz => by
      simp only [us, hRtarget] at hz
      rcases hReq (hθ hz) with h1 | ⟨h2, -⟩
      · exact h1
      · exact absurd hl h2)
    (fun l hl h => by
      have := hδinj h
      exact hl (this ▸ τs_mem c _))
    (fun l hl => hθS ⟨l, hl⟩)
  -- 3. the line is eventually injective
  have hinj : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), Function.Injective (uline us δ ε) := by
    have hpair : ∀ p : Fin M × Fin M, ∀ᶠ ε in 𝓝[≠] (0 : ℝ), p.1 ≠ p.2 →
        uline us δ ε p.1 ≠ uline us δ ε p.2 := by
      intro p
      by_cases hR : R p.1 = R p.2
      · filter_upwards [self_mem_nhdsWithin] with ε hε hne
        simp only [uline, us, hR]
        intro h
        have : ε * (δ p.1 - δ p.2) = 0 := by linarith
        rcases mul_eq_zero.mp this with h1 | h1
        · exact hε h1
        · exact hne (hδinj (sub_eq_zero.mp h1))
      · have hlim := (uline_tendsto us δ p.1).sub (uline_tendsto us δ p.2)
        have hne : us p.1 - us p.2 ≠ 0 := sub_ne_zero.mpr (fun h => hR (hθ h))
        filter_upwards [hlim.eventually_ne hne] with ε hε _
        exact fun h => hε (by rw [h, sub_self])
    filter_upwards [eventually_all.mpr hpair] with ε hε
    intro i j hij
    by_contra hne
    exact hε (i, j) hne hij
  obtain ⟨ε, hε1, hε2⟩ := (hev.and hinj).exists
  exact ⟨uline us δ ε, hε2, hε1⟩

/-- `exists_good_u` (`GenericHK.lean`) with the conclusion of `Lval_ne_zero` as a hypothesis `hL`;
otherwise a verbatim copy. -/
theorem exists_good_u_of_Lval {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    {t : Fin M → Fin M → ℝ}
    (hL : ∀ (us : Fin M → ℝ) (π a : Fin M), π ≠ a → (∀ q, q ≠ a → q ≠ π → us q < us a) →
      Lval G t us π a π ≠ 0) (c : Conf M N)
    {κ : Type*} [Finite κ] (R : κ → MvPolynomial (Fin M) ℝ) (hR0 : ∀ k, R k ≠ 0) :
    ∃ u : Fin M → ℝ, ∃ hw : Function.Injective (wC u : Conf M N → ℝ),
      (∀ y, alphaRep (Γ (-hopM G t)) (wC u) hw (mopt G c) (lip_mopt hG t c) c
        (mopt_self G c) y y ≠ 0) ∧ ∀ k, eval u (R k) ≠ 0 := by
  classical
  have := Fintype.ofFinite κ
  -- polynomial conditions: distinct configuration energies and multiset genericity
  set κ1 := {p : Conf M N × Conf M N // p.1 ≠ p.2}
  set κ2 := {p : Conf M N × (Fin N → Fin M) // ¬ ∃ ρ : Equiv.Perm (Fin N), ∀ l, p.2 l =
      τs p.1 (ρ l)}
  obtain ⟨u, hu, hD, hR⟩ := exists_common_ne (κ := (κ1 ⊕ κ2) ⊕ κ)
    (fun y : Conf M N => fun u => DExp G t u c y) (fun y => ratOn_DExp G t c y)
    (fun y => exists_DExp_ne_of_Lval hG hL c y)
    (Sum.elim (Sum.elim (fun p : κ1 => formW p.1.1 p.1.2) (fun p : κ2 => formZ p.1.1 p.1.2)) R)
    (fun k => by
      rcases k with (p | p) | k
      · exact formW_ne_zero p.2
      · exact formZ_ne_zero p.2
      · exact hR0 k)
  have hw : Function.Injective (wC u : Conf M N → ℝ) := by
    intro s s' h
    by_contra hne
    have := hR (Sum.inl (Sum.inl ⟨(s, s'), hne⟩))
    simp only [Sum.elim_inl, eval_formW, h, sub_self] at this
    exact this rfl
  have hgen : ∀ y : Conf M N, ∀ z : Fin N → Fin M, ∑ l, u (z l) = wC u y →
      ∃ ρ : Equiv.Perm (Fin N), ∀ l, z l = τs y (ρ l) := by
    intro y z hz
    by_contra hne
    have := hR (Sum.inl (Sum.inr ⟨(y, z), hne⟩))
    simp only [Sum.elim_inl, Sum.elim_inr, eval_formZ, hz, sub_self] at this
    exact this rfl
  refine ⟨u, hw, fun y => ?_, fun k => by simpa using hR (Sum.inr k)⟩
  rw [alpha_eq_D hG t u hu hw c y (hgen y), D_eq_DExp hG t hu c y]
  exact hD y

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
      ∀ v, NonUV (H0Fw G t Vint) (occF : Fin M → Conf M N → ℝ) v → eval v P = 0 := by
  classical
  set ord : Conf M N → ℕ := fun j => (Fintype.equivFin (Conf M N) j : ℕ)
  refine ⟨∏ c, krylovPoly (H0Fw G t Vint) occF c ord,
    Finset.prod_ne_zero_iff.mpr (fun c _ => hstar_lattice_fermions_shortest hG hsp c Vint),
    fun v hv => ?_⟩
  obtain ⟨c, hc⟩ :=
    nonUV_imp_krylov_zero (H0Fw_isSymm G htsym Vint) (rigid_occF hN0 hNM) hv ord
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ c) hc

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

/-- Hopping of a common sign is `ShortestPathSigned` (`ε q = 1` for `s > 0`,
`ε q = (-1)^dist(b, q)` otherwise). -/
theorem shortestPathSigned_of_common_sign {G : SimpleGraph (Fin M)} {t : Fin M → Fin M → ℝ}
    {s : ℝ} (hts : ∀ a b, G.Adj a b → 0 < s * t a b) : ShortestPathSigned G t := by
  intro b
  by_cases hs : 0 < s
  · refine ⟨fun _ => 1, fun _ => by norm_num, fun q r hqr _ => ?_⟩
    have := (pos_iff_pos_of_mul_pos (hts q r hqr)).mp hs
    simpa using this
  · refine ⟨fun q => (-1) ^ G.dist b q, fun q => by rw [← mul_pow]; norm_num,
      fun q r hqr hd => ?_⟩
    have h := hts q r hqr
    have ht : t q r < 0 := by
      by_contra hc; push Not at hc; push Not at hs; nlinarith
    have h1 : ((-1 : ℝ) ^ G.dist b r) * (-1) ^ G.dist b r = 1 := by rw [← mul_pow]; norm_num
    simp only
    rw [← hd, pow_succ]
    have e : (-1 : ℝ) ^ G.dist b r * -1 * t q r * (-1) ^ G.dist b r =
        -t q r * ((-1 : ℝ) ^ G.dist b r * (-1) ^ G.dist b r) := by ring
    rw [e, h1]; linarith

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
