/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Positivity

public import LeanPool.ApollonianSuperharmonic.P3723T1AllContactRouting
public import LeanPool.ApollonianSuperharmonic.P3776T1FixedGeometry
public import Mathlib.Analysis.Normed.MulAction

-- [TABLET NODE: P3889T1ExactRadialStar]

/-!
# P3889T1ExactRadialStar

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RadialStarProof

private theorem hposition_arc_endpoint :
    ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀
        [Nontrivial ι], (∀ (c : ι), ∀ (d : ι), (P.plane.adjacent c d) → (P3723T1EdgeContact P c
        d)) → (∀ (v : ι), ∀ (c : ι), ∀ (d : ι), P3723T1EdgeContact P c d → D.position v ∈
        D.edgeArc c d → v = c ∨ v = d) := by
  classical
  intro ι P D this hadj_contact v c d hcd hv
  obtain ⟨w, hvw⟩ := (P3767T1VertexEdgeIncidence P.plane v).1
  have hvwContact := hadj_contact v w hvw
  have hstart : D.position v ∈ D.edgeArc v w := by
    obtain ⟨g, _, _, hrange, hg0, _, _⟩ := D.edgeArc_parameterization v w hvwContact
    rw [← hrange, ← hg0]
    exact ⟨⟨0, by norm_num⟩, rfl⟩
  by_cases heq : ({v, w} : Set ι) = {c, d}
  · have hvmem : v ∈ ({c, d} : Set ι) := heq ▸ (by simp)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hvmem
  · have hmem : D.position v ∈ D.position '' (({v, w} : Set ι) ∩ {c, d}) := by
      rw [← D.edgeArc_intersections v w c d hvwContact hcd heq]
      exact ⟨hstart, hv⟩
    obtain ⟨z, hz, hzpos⟩ := hmem
    have hzv : z = v := D.position_injective hzpos
    subst z
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz.2

private theorem hlocal :
    ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (a : ι),
        (∀ (c : ι), ∀ (d : ι), (P.plane.adjacent c d) → (P3723T1EdgeContact P c d)) → (∀ (c :
        ι), P.plane.adjacent a c → ∃ (u : ℝ × ℝ), ‖u‖ = (1 : ℝ) ∧ ∃ ε > (0 : ℝ), D.edgeArc a c ∩
        Metric.ball (D.position a) ε = Metric.ball (D.position a) ε ∩ {p : ℝ × ℝ | ∃ (t : ℝ), (0
        : ℝ) ≤ t ∧ p = D.position a + t • u}) := by
  classical
  intro ι P D a hadj_contact c hac
  obtain ⟨g, hcont, hinj, hrange, hg0, _, ⟨cert⟩⟩ :=
    D.edgeArc_parameterization a c (hadj_contact a c hac)
  let i : Fin cert.count := ⟨0, cert.positive⟩
  let τ := cert.time i.succ
  have hτ : 0 < τ := by
    have hi : i.castSucc < i.succ := by
      change (0 : Nat) < 1
      omega
    have := cert.strict hi
    simpa [τ, i, cert.start] using this
  have htime0 : cert.time i.castSucc = 0 := by
    have hi : i.castSucc = (0 : Fin (cert.count + 1)) := by ext; rfl
    rw [hi, cert.start]
  obtain ⟨A, B, hseg⟩ := cert.affine_on i
  let σ := τ / 2
  have hσ : 0 < σ ∧ σ < τ := by dsimp [σ]; constructor <;> linarith
  let s0 : Set.Icc (0 : Real) 1 := ⟨0, by norm_num⟩
  have hτle : τ ≤ 1 := by
    dsimp [τ]
    calc
      cert.time i.succ ≤ cert.time (Fin.last cert.count) :=
        cert.strict.monotone (Fin.le_last _)
      _ = 1 := cert.finish
  let sσ : Set.Icc (0 : Real) 1 := ⟨σ, le_of_lt hσ.1, le_trans (le_of_lt hσ.2) hτle⟩
  have hlo0 : cert.time i.castSucc ≤ (s0 : Real) := by rw [htime0]
  have hhi0 : (s0 : Real) ≤ cert.time i.succ := by
    change 0 ≤ cert.time i.succ
    exact le_of_lt hτ
  have hseg0 : g s0 = A := by simpa [s0] using hseg s0 hlo0 hhi0
  have hA : A = D.position a := hseg0.symm.trans hg0
  have hlosigma : cert.time i.castSucc ≤ (sσ : Real) := by
    rw [htime0]
    exact le_of_lt hσ.1
  have hhisigma : (sσ : Real) ≤ cert.time i.succ := le_of_lt hσ.2
  have hsegsigma : g sσ = D.position a + σ • B := by
    simpa [sσ] using (hseg sσ hlosigma hhisigma).trans (by rw [hA])
  have hB : B ≠ 0 := by
    intro hzero
    have hsame : g sσ = g s0 := by
      rw [hsegsigma, hzero, smul_zero, add_zero]
      exact (hseg0.trans hA).symm
    have : sσ = s0 := hinj (by simpa [s0] using hsame)
    have : σ = 0 := congrArg (fun s : Set.Icc (0 : Real) 1 => (s : Real)) this
    linarith [hσ.1]
  let u : Real × Real := ‖B‖⁻¹ • B
  have hnorm : ‖u‖ = 1 := by
    change ‖‖B‖⁻¹ • B‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hB))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hB)
  let tail : Set (Set.Icc (0 : Real) 1) := {s | σ ≤ (s : Real)}
  have htailclosed : IsClosed tail := by
    dsimp [tail]
    exact isClosed_Ici.preimage continuous_subtype_val
  have htailparam : IsCompact tail :=
    isCompact_univ.of_isClosed_subset htailclosed (by intro s hs; trivial)
  have htail : IsCompact (g '' tail) := htailparam.image hcont
  have hxnot : D.position a ∉ g '' tail := by
    rintro ⟨s, hs, hgs⟩
    have heq : s = s0 := hinj (by simpa [s0] using hgs.trans hg0.symm)
    rw [heq] at hs
    exact (not_lt_of_ge hs) hσ.1
  obtain ⟨ε₀, hε₀, hball₀⟩ := (Metric.isOpen_iff.mp htail.isClosed.isOpen_compl)
    (D.position a) hxnot
  let ε := min ε₀ (σ * ‖B‖) / 2
  have hlenpos : 0 < σ * ‖B‖ := mul_pos hσ.1 (norm_pos_iff.mpr hB)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε < ε₀ := by dsimp [ε]; have := min_le_left ε₀ (σ * ‖B‖); linarith
  have hεlen : ε < σ * ‖B‖ := by dsimp [ε]; have := min_le_right ε₀ (σ * ‖B‖); linarith
  have hball : Metric.ball (D.position a) ε ⊆ (g '' tail)ᶜ := by
    exact (Metric.ball_subset_ball (le_of_lt hεδ)).trans hball₀
  refine ⟨u, hnorm, ε, hε, ?_⟩
  -- The two inclusions use the first affine segment and the omitted compact tail.
  ext p
  constructor
  · rintro ⟨hpArc, hpBall⟩
    rw [← hrange] at hpArc
    obtain ⟨s, hsrep⟩ := hpArc
    by_cases hs : σ ≤ (s : Real)
    · exact False.elim (hball hpBall ⟨s, hs, hsrep⟩)
    · have hsσ : (s : Real) < σ := lt_of_not_ge hs
      have hlos : cert.time i.castSucc ≤ (s : Real) := by
        rw [htime0]
        exact s.property.1
      have hhis : (s : Real) ≤ cert.time i.succ := by
        change (s : Real) ≤ τ
        exact le_of_lt (hsσ.trans hσ.2)
      have hseg_s : g s = D.position a + (s : Real) • B := by
        rw [hseg s hlos hhis, hA]
      have hscale : (s : Real) • B = ((s : Real) * ‖B‖) • u := by
        dsimp [u]
        rw [smul_smul]
        congr 1
        field_simp
      refine ⟨hpBall, ?_⟩
      refine ⟨(s : Real) * ‖B‖,
        mul_nonneg s.property.1 (norm_nonneg _), ?_⟩
      calc
        p = g s := hsrep.symm
        _ = D.position a + (s : Real) • B := hseg_s
        _ = D.position a + ((s : Real) * ‖B‖) • u := by rw [hscale]
  · rintro ⟨hpBall, t, ht, rfl⟩
    have htbound : t < ε := by
      have hdist : dist (D.position a + t • u) (D.position a) = t := by
        rw [dist_eq_norm]
        simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hnorm]
      simpa [Metric.mem_ball, hdist] using hpBall
    let s : Set.Icc (0 : Real) 1 := ⟨t / ‖B‖, by
      constructor
      · exact div_nonneg ht (norm_nonneg _)
      · have hlen : ε < σ * ‖B‖ := hεlen
        have hnB : 0 < ‖B‖ := norm_pos_iff.mpr hB
        apply (div_le_iff₀ hnB).2
        nlinarith [htbound, hlen]
      ⟩
    have hlo_s : cert.time i.castSucc ≤ (s : Real) := by
      rw [htime0]
      exact div_nonneg ht (norm_nonneg _)
    have hlen : ε < σ * ‖B‖ := hεlen
    have hquot : t / ‖B‖ < σ := (div_lt_iff₀ (norm_pos_iff.mpr hB)).2 (by nlinarith [htbound, hlen])
    have hhi_s : (s : Real) ≤ cert.time i.succ := by
      change t / ‖B‖ ≤ τ
      exact (le_of_lt hquot).trans (le_of_lt hσ.2)
    have hseg_s : g s = D.position a + (s : Real) • B := by
      rw [hseg s hlo_s hhi_s, hA]
    have hscale : (t / ‖B‖) • B = t • u := by
      dsimp [u]
      rw [smul_smul]
      congr 1
    have hsval : g s = D.position a + t • u := by
      calc
        g s = D.position a + (s : Real) • B := hseg_s
        _ = D.position a + t • u := by rw [hscale]
    have hgsArc : g s ∈ D.edgeArc a c := by
      rw [← hrange]
      exact ⟨s, rfl⟩
    have hgsBall : g s ∈ Metric.ball (D.position a) ε := by
      simpa [hsval] using hpBall
    exact ⟨hsval ▸ hgsArc, hsval ▸ hgsBall⟩

private theorem finiteLower :
    ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (a : ι),
        ∀ (hlocal : ∀ (c : ι), (P.plane.adjacent a c) → (∃ u : Real × Real, ‖u‖ = 1 ∧ ∃ ε > 0,
        D.edgeArc a c ∩ Metric.ball (D.position a) ε = Metric.ball (D.position a) ε ∩ {p | ∃ t :
        Real, 0 ≤ t ∧ p = D.position a + t • u})),
    let localEps (c : ι) (hc : P.plane.adjacent a c) : Real :=
      Classical.choose (Classical.choose_spec (hlocal c hc)).2
    let eps (c : ι) : Real := @dite Real (P.plane.adjacent a c) (Classical.propDecidable _)
        (fun hc => localEps c hc) (fun _ => 1)
    ∀ s : Finset ι, (∀ c ∈ s, 0 < eps c) → ∃ q : Real, 0 < q ∧ ∀ c ∈ s, q < eps c := by
  classical
  intro ι P D a hlocal localEps eps s
  induction s using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨1, by norm_num, by simp⟩
  | @insert c s hcs ih =>
      intro hpos
      obtain ⟨q, hq, hqsmall⟩ := ih (by
        intro d hd
        exact hpos d (Finset.mem_insert_of_mem hd))
      let q' := min q (eps c) / 2
      have hcur : 0 < eps c := hpos c (Finset.mem_insert_self c s)
      have hq' : 0 < q' := by
        dsimp [q']
        positivity
      refine ⟨q', hq', ?_⟩
      intro d hd
      rcases Finset.mem_insert.mp hd with hdc | hd
      · have hdc' : d = c := hdc
        subst d
        dsimp [q']
        have hm := min_le_right q (eps c)
        linarith
      · dsimp [q']
        have hm := min_le_left q (eps c)
        have := hqsmall d hd
        linarith

private theorem localRay :
    ∀ (ι : Type),
      ∀ (P : PeriodicTileComplex ι),
        ∀ (D : P3723T1AllContactRouting P),
          ∀ (a : ι),
            ∀
              (hlocal :
                ∀ (c : ι),
                  P.plane.adjacent a c →
                    ∃ u : Real × Real,
                      ‖u‖ = 1 ∧
                        ∃ ε > 0,
                          D.edgeArc a c ∩ Metric.ball (D.position a) ε =
                            Metric.ball (D.position a) ε ∩
                            {p | ∃ t : Real, 0 ≤ t ∧ p = D.position a + t • u}),
              let localU (c : ι) (hc : P.plane.adjacent a c) : Real × Real :=
                Classical.choose (hlocal c hc);
              let localEps (c : ι) (hc : P.plane.adjacent a c) : Real :=
                Classical.choose (Classical.choose_spec (hlocal c hc)).2;
              (∀ (c : ι),
                  ∀ (hc : P.plane.adjacent a c),
                    ‖localU c hc‖ = 1 ∧
                      0 < localEps c hc ∧
                        D.edgeArc a c ∩ Metric.ball (D.position a) (localEps c hc) =
                          Metric.ball (D.position a) (localEps c hc) ∩
                            {p | ∃ t : Real, 0 ≤ t ∧ p = D.position a + t • localU c hc}) →
                let u : ι → Real × Real := fun c =>
                  @dite (Real × Real) (P.plane.adjacent a c) (Classical.propDecidable _)
                    (fun hc => localU c hc) fun _ => 0;
                ∀ (c : ι),
                  ∀ (hc : P.plane.adjacent a c),
                    ∀ (q : ℝ),
                      q < localEps c hc →
                        D.edgeArc a c ∩ Metric.ball (D.position a) q =
                          Metric.ball (D.position a) q ∩
                            {p : ℝ × ℝ |
                            ∃ (t : ℝ), (0 : ℝ) ≤ t ∧ p = D.position a + t • u c} := by
  classical
  intro ι P D a hlocal localU localEps localSpec u c hc q hq
  have heq := (localSpec c hc).2.2
  have hball : Metric.ball (D.position a) q ⊆
      Metric.ball (D.position a) (localEps c hc) :=
    Metric.ball_subset_ball (le_of_lt hq)
  ext p
  constructor
  · rintro ⟨hpa, hpb⟩
    have hbig : p ∈ Metric.ball (D.position a) (localEps c hc) := hball hpb
    have hray : p ∈ {p | ∃ t : Real, 0 ≤ t ∧
        p = D.position a + t • localU c hc} := by
      have : p ∈ D.edgeArc a c ∩ Metric.ball (D.position a) (localEps c hc) := ⟨hpa, hbig⟩
      rw [heq] at this
      exact this.2
    rcases hray with ⟨t, ht, hp⟩
    exact ⟨hpb, t, ht, by simpa [u, hc] using hp⟩
  · rintro ⟨hpb, t, ht, hp⟩
    have hbig : p ∈ Metric.ball (D.position a) (localEps c hc) := hball hpb
    have hray : p ∈ {p | ∃ t : Real, 0 ≤ t ∧
        p = D.position a + t • localU c hc} := by
      exact ⟨t, ht, by simpa [u, hc] using hp⟩
    have : p ∈ Metric.ball (D.position a) (localEps c hc) ∩
        {p | ∃ t : Real, 0 ≤ t ∧ p = D.position a + t • localU c hc} := ⟨hbig, hray⟩
    rw [← heq] at this
    exact ⟨this.1, hpb⟩

private theorem hforeign :
    ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (a : ι),
        (∀ (c : ι), ∀ (d : ι), (P.plane.adjacent c d) → (P3723T1EdgeContact P c d)) → (∀ (rN : ℝ),
    let Q : Set (Real × Real) := Metric.closedBall (D.position a) 1
    let E : Set (ι × ι) := {e | P3723T1EdgeContact P e.1 e.2 ∧
        (D.edgeArc e.1 e.2 ∩ Q).Nonempty}
    let E0 : Set (ι × ι) := {e | e ∈ E ∧ e.1 ≠ a ∧ e.2 ≠ a}
    let A : Set (Real × Real) := ⋃ e ∈ E0, D.edgeArc e.1 e.2
    ∀ (rF0 : ℝ), (Metric.ball (D.position a) rF0 ⊆ Aᶜ) → (
    let r : Real := min rN (min rF0 1) / 2
    (r < rF0) → ((r < 1) → (∀ (c : ι), ∀ (d : ι), P.plane.adjacent c d → c ≠ a → d ≠ a → Disjoint
        (D.edgeArc c d) (Metric.ball (D.position a) r))))) := by
  classical
  intro ι P D a hadj_contact rN Q E E0 A rF0 hballF r hrFlt hrlt1 c d hcd hca hda
  apply Set.disjoint_left.mpr
  intro p hpArc hpBall
  have hpdist : dist p (D.position a) < r := Metric.mem_ball.mp hpBall
  have hpQ : p ∈ Q := by
    apply Metric.mem_closedBall.mpr
    exact le_of_lt (hpdist.trans hrlt1)
  have hcontact := hadj_contact c d hcd
  have he : (c, d) ∈ E := by
    change P3723T1EdgeContact P c d ∧ (D.edgeArc c d ∩ Q).Nonempty
    exact ⟨hcontact, ⟨p, ⟨hpArc, hpQ⟩⟩⟩
  have hpA : p ∈ A := by
    change p ∈ ⋃ e : ι × ι, ⋃ (_ : e ∈ E0), D.edgeArc e.1 e.2
    exact Set.mem_iUnion.mpr ⟨(c, d), Set.mem_iUnion.mpr
      ⟨⟨he, hca, hda⟩, hpArc⟩⟩
  have hpAF : p ∈ Aᶜ := hballF (Metric.mem_ball.mpr (hpdist.trans hrFlt))
  exact hpAF hpA

private theorem hu_injective :
    ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (a : ι),
        (∀ (c : ι), ∀ (d : ι), (P.plane.adjacent c d) → (P3723T1EdgeContact P c d)) → (∀
        (hlocal : ∀ (c : ι), (P.plane.adjacent a c) → (∃ u : Real × Real, ‖u‖ = 1 ∧ ∃ ε > 0,
        D.edgeArc a c ∩ Metric.ball (D.position a) ε = Metric.ball (D.position a) ε ∩ {p | ∃ t :
        Real, 0 ≤ t ∧ p = D.position a + t • u})),
    let localU (c : ι) (hc : P.plane.adjacent a c) : Real × Real :=
      Classical.choose (hlocal c hc)
    let localEps (c : ι) (hc : P.plane.adjacent a c) : Real :=
      Classical.choose (Classical.choose_spec (hlocal c hc)).2
    ∀ (rN : ℝ),
    let u : ι → Real × Real := fun c =>
      @dite (Real × Real) (P.plane.adjacent a c) (Classical.propDecidable _)
        (fun hc => localU c hc) (fun _ => 0)
    (∀ (c : ι), (P.plane.adjacent a c) → (‖u c‖ = 1)) → ((∀ (c : ι), ∀ (hc : P.plane.adjacent a
        c), ∀ (q : Real), (0 < q) → ((q < localEps c hc) → (D.edgeArc a c ∩ Metric.ball
        (D.position a) q = Metric.ball (D.position a) q ∩ {p | ∃ t : Real, 0 ≤ t ∧ p = D.position
        a + t • u c}))) → (∀ (rF0 : ℝ),
    let r : Real := min rN (min rF0 1) / 2
    (0 < r) → ((∀ (c : ι), ∀ (hc : P.plane.adjacent a c), r < localEps c hc) → (∀ c, ∀ d,
        P.plane.adjacent a c → P.plane.adjacent a d → u c = u d → c = d))))) := by
  classical
  intro ι P D a hadj_contact hlocal localU localEps rN u u_norm localRay rF0 r hr hr_local c d
      hac had hdirs
  by_contra hne
  have hca : c ≠ a := by
    intro h
    subst c
    exact P.plane.adjacent_irreflexive a hac
  have hda : d ≠ a := by
    intro h
    subst d
    exact P.plane.adjacent_irreflexive a had
  let p := D.position a + (r / 2) • u c
  have hhalf : 0 < r / 2 := by linarith
  have hpnorm : ‖(r / 2) • u c‖ = r / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hhalf, u_norm c hac]
    ring
  have hpball : p ∈ Metric.ball (D.position a) r := by
    rw [Metric.mem_ball, dist_eq_norm]
    dsimp [p]
    simp [hpnorm]
    linarith
  have hrayc : p ∈ {p | ∃ t : Real, 0 ≤ t ∧ p = D.position a + t • u c} :=
    ⟨r / 2, le_of_lt hhalf, rfl⟩
  have hrayd : p ∈ {p | ∃ t : Real, 0 ≤ t ∧ p = D.position a + t • u d} := by
    simpa [hdirs] using hrayc
  have hAc : p ∈ D.edgeArc a c := by
    have hmem : p ∈ D.edgeArc a c ∩ Metric.ball (D.position a) r := by
      rw [localRay c hac r hr (hr_local c hac)]
      exact ⟨hpball, hrayc⟩
    exact hmem.1
  have hAd : p ∈ D.edgeArc a d := by
    have hmem : p ∈ D.edgeArc a d ∩ Metric.ball (D.position a) r := by
      rw [localRay d had r hr (hr_local d had)]
      exact ⟨hpball, hrayd⟩
    exact hmem.1
  have hsetne : ({a, c} : Set ι) ≠ {a, d} := by
    intro hsets
    have hmem : d ∈ ({a, c} : Set ι) := hsets.symm ▸ (by simp)
    have : d = c := by simpa [hda] using hmem
    exact hne this.symm
  have hint := D.edgeArc_intersections a c a d
    (hadj_contact a c hac) (hadj_contact a d had) hsetne
  have hpimage : p ∈ D.position '' (({a, c} : Set ι) ∩ {a, d}) := by
    rw [← hint]
    exact ⟨hAc, hAd⟩
  obtain ⟨v, hv, hvp⟩ := hpimage
  have hva : v = a := by
    have hv1 : v = a ∨ v = c := by simpa using hv.1
    have hv2 : v = a ∨ v = d := by simpa using hv.2
    rcases hv1 with h | h
    · exact h
    · rcases hv2 with h' | h'
      · exact h'
      · exact (hne (h.symm.trans h')).elim
  subst v
  have : p = D.position a := hvp.symm
  have hzero : (r / 2) • u c = 0 := by
    have hsub := congrArg (fun x : Real × Real => x - D.position a) this
    simpa [p] using hsub
  have hnormzero := congrArg (fun x : Real × Real => ‖x‖) hzero
  rw [hpnorm, norm_zero] at hnormzero
  linarith

private theorem vertexRay :
    ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (a : ι),
        ∀ [Nontrivial ι], ∀ (hlocal : ∀ (c : ι), (P.plane.adjacent a c) → (∃ u : Real × Real, ‖u‖
        = 1 ∧ ∃ ε > 0, D.edgeArc a c ∩ Metric.ball (D.position a) ε = Metric.ball (D.position a)
        ε ∩ {p | ∃ t : Real, 0 ≤ t ∧ p = D.position a + t • u})),
    let localU (c : ι) (hc : P.plane.adjacent a c) : Real × Real :=
      Classical.choose (hlocal c hc)
    let localEps (c : ι) (hc : P.plane.adjacent a c) : Real :=
      Classical.choose (Classical.choose_spec (hlocal c hc)).2
    ∀ (rN : ℝ),
    let u : ι → Real × Real := fun c =>
      @dite (Real × Real) (P.plane.adjacent a c) (Classical.propDecidable _)
        (fun hc => localU c hc) (fun _ => 0)
    (∀ (c : ι), ∀ (hc : P.plane.adjacent a c), ∀ (q : Real), (0 < q) → ((q < localEps c hc) →
        (D.edgeArc a c ∩ Metric.ball (D.position a) q = Metric.ball (D.position a) q ∩ {p | ∃ t :
        Real, 0 ≤ t ∧ p = D.position a + t • u c}))) → (∀ (rF0 : ℝ),
    let r : Real := min rN (min rF0 1) / 2
    (0 < r) → ((∀ (c : ι), ∀ (hc : P.plane.adjacent a c), r < localEps c hc) → ((∀ (c : ι), ∀ (d
        : ι), (P.plane.adjacent c d) → ((c ≠ a) → ((d ≠ a) → (Disjoint (D.edgeArc c d)
        (Metric.ball (D.position a) r))))) → ((∀ (v : ι), ∀ (w : ι), (P.plane.adjacent v w) →
        (D.position v ∈ D.edgeArc v w)) → (∀ (v : ι), D.position v ∈ Metric.ball (D.position a) r
        → ∃ (c : ι), P.plane.adjacent a c ∧ ∃ (t : ℝ), (0 : ℝ) ≤ t ∧ D.position v = D.position a
        + t • u c))))) := by
  classical
  intro ι P D a this hlocal localU localEps rN u localRay rF0 r hr hr_local hforeign vertexArc v
      hvball
  by_cases hva : v = a
  · subst v
    obtain ⟨c, hac⟩ := (P3767T1VertexEdgeIncidence P.plane a).1
    exact ⟨c, hac, 0, le_rfl, by simp⟩
  · obtain ⟨w, hvw⟩ := (P3767T1VertexEdgeIncidence P.plane v).1
    have hvArc := vertexArc v w hvw
    by_cases hwa : w = a
    · subst w
      have haw : P.plane.adjacent a v := (P.plane.adjacent_symmetric v a).mp hvw
      have harc : D.position v ∈ D.edgeArc a v := by
        rw [D.edgeArc_symmetric v a] at hvArc
        exact hvArc
      have hmem : D.position v ∈ D.edgeArc a v ∩ Metric.ball (D.position a) r :=
        ⟨harc, hvball⟩
      rw [localRay v haw r hr (hr_local v haw)] at hmem
      rcases hmem.2 with ⟨t, ht, hp⟩
      exact ⟨v, haw, t, ht, hp⟩
    · have hfalse := (Set.disjoint_left.mp
        (hforeign v w hvw hva hwa)) hvArc hvball
      exact False.elim hfalse

end RadialStarProof

theorem P3889T1ExactRadialStar {ι : Type} (P : PeriodicTileComplex ι)
    (D : P3723T1AllContactRouting P) (a : ι) :
    ∃ r : Real, 0 < r ∧ ∃ u : ι → Real × Real,
      (∀ c, P.plane.adjacent a c → ‖u c‖ = 1) ∧
      (∀ c d, P.plane.adjacent a c → P.plane.adjacent a d →
        u c = u d → c = d) ∧
      (∀ c, P.plane.adjacent a c →
        D.edgeArc a c ∩ Metric.ball (D.position a) r =
          Metric.ball (D.position a) r ∩
            {p | ∃ t : Real, 0 ≤ t ∧ p = D.position a + t • u c}) ∧
      (∀ c d, P.plane.adjacent c d → c ≠ a → d ≠ a →
        Disjoint (D.edgeArc c d) (Metric.ball (D.position a) r)) ∧
      ((Set.range D.position ∪
          {p | ∃ c d, P.plane.adjacent c d ∧ p ∈ D.edgeArc c d}) ∩
          Metric.ball (D.position a) r =
        Metric.ball (D.position a) r ∩
          {p | ∃ c, P.plane.adjacent a c ∧
            ∃ t : Real, 0 ≤ t ∧ p = D.position a + t • u c}) := by
-- BODY
  classical
  let : Nontrivial ι := P3776T1FixedGeometry P.toPeriodicTileCore |>.1
  have hadj_contact (c d : ι) (hcd : P.plane.adjacent c d) :
      P3723T1EdgeContact P c d := by
    refine ⟨?_, P.adjacent_has_common_edge c d hcd⟩
    intro h
    subst d
    exact P.plane.adjacent_irreflexive c hcd
  have hposition_arc_endpoint (v c d : ι) (hcd : P3723T1EdgeContact P c d)
      (hv : D.position v ∈ D.edgeArc c d) : v = c ∨ v = d :=
          RadialStarProof.hposition_arc_endpoint ι P D  hadj_contact v c d hcd hv
  have hincident_position (c : ι) (hac : P.plane.adjacent a c) :
      D.position a ∈ D.edgeArc a c := by
    obtain ⟨g, _, _, hrange, hg0, _, _⟩ := D.edgeArc_parameterization a c (hadj_contact a c hac)
    rw [← hrange]
    rw [← hg0]
    exact ⟨⟨0, by norm_num⟩, rfl⟩
  have hlocal (c : ι) (hac : P.plane.adjacent a c) :
      ∃ u : Real × Real, ‖u‖ = 1 ∧ ∃ ε > 0,
        D.edgeArc a c ∩ Metric.ball (D.position a) ε =
          Metric.ball (D.position a) ε ∩
            {p | ∃ t : Real, 0 ≤ t ∧ p = D.position a + t • u} := RadialStarProof.hlocal ι P D a
                hadj_contact c hac
  have hNfin : Set.Finite {c : ι | P.plane.adjacent a c} := P.plane.locally_finite a
  let localU (c : ι) (hc : P.plane.adjacent a c) : Real × Real :=
    Classical.choose (hlocal c hc)
  let localEps (c : ι) (hc : P.plane.adjacent a c) : Real :=
    Classical.choose (Classical.choose_spec (hlocal c hc)).2
  have localSpec (c : ι) (hc : P.plane.adjacent a c) :
      ‖localU c hc‖ = 1 ∧ 0 < localEps c hc ∧
        D.edgeArc a c ∩ Metric.ball (D.position a) (localEps c hc) =
          Metric.ball (D.position a) (localEps c hc) ∩
            {p | ∃ t : Real, 0 ≤ t ∧ p = D.position a + t • localU c hc} := by
    dsimp [localU, localEps]
    have hs := Classical.choose_spec (hlocal c hc)
    have he := Classical.choose_spec hs.2
    exact ⟨hs.1, he.1, he.2⟩
  let eps (c : ι) : Real := @dite Real (P.plane.adjacent a c) (Classical.propDecidable _)
        (fun hc => localEps c hc) (fun _ => 1)
  have finiteLower : ∀ s : Finset ι,
      (∀ c ∈ s, 0 < eps c) →
        ∃ q : Real, 0 < q ∧ ∀ c ∈ s, q < eps c := RadialStarProof.finiteLower ι P D a hlocal
  let SN := hNfin.toFinset
  obtain ⟨rN, hrN, hrNsmall⟩ := finiteLower SN (by
    intro c hc
    have hca : P.plane.adjacent a c := (Set.Finite.mem_toFinset hNfin).mp hc
    simpa [eps, hca] using (localSpec c hca).2.1)
  let u : ι → Real × Real := fun c =>
    @dite (Real × Real) (P.plane.adjacent a c) (Classical.propDecidable _)
        (fun hc => localU c hc) (fun _ => 0)
  have u_norm (c : ι) (hc : P.plane.adjacent a c) : ‖u c‖ = 1 := by
    simp [u, hc, localSpec c hc]
  have localRay (c : ι) (hc : P.plane.adjacent a c) (q : Real)
      (hq0 : 0 < q) (hq : q < localEps c hc) :
      D.edgeArc a c ∩ Metric.ball (D.position a) q =
        Metric.ball (D.position a) q ∩
          {p | ∃ t : Real, 0 ≤ t ∧ p = D.position a + t • u c} := RadialStarProof.localRay ι P D
              a hlocal localSpec c hc q hq
  have edgeCompact (c d : ι) (hcd : P3723T1EdgeContact P c d) :
      IsCompact (D.edgeArc c d) := by
    obtain ⟨g, hg, _, hrange, _, _, _⟩ := D.edgeArc_parameterization c d hcd
    let : CompactSpace (Set.Icc (0 : Real) 1) := inferInstance
    rw [← hrange]
    exact isCompact_range hg
  let Q : Set (Real × Real) := Metric.closedBall (D.position a) 1
  have hQ : IsCompact Q := by dsimp [Q]; exact isCompact_closedBall _ _
  let E : Set (ι × ι) := {e | P3723T1EdgeContact P e.1 e.2 ∧
      (D.edgeArc e.1 e.2 ∩ Q).Nonempty}
  have hE : E.Finite := by
    dsimp [E, Q]
    exact D.compact_local_finiteness _ (isCompact_closedBall _ _)
  let E0 : Set (ι × ι) := {e | e ∈ E ∧ e.1 ≠ a ∧ e.2 ≠ a}
  have hE0 : E0.Finite := hE.subset (by intro e he; exact he.1)
  let A : Set (Real × Real) := ⋃ e ∈ E0, D.edgeArc e.1 e.2
  have hAcompact : IsCompact A := by
    dsimp [A]
    apply hE0.isCompact_biUnion
    intro e he
    exact edgeCompact e.1 e.2 he.1.1
  have hxA : D.position a ∉ A := by
    change D.position a ∉ ⋃ e : ι × ι, ⋃ (_ : e ∈ E0), D.edgeArc e.1 e.2
    intro hx
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
    obtain ⟨he0, hx⟩ := Set.mem_iUnion.mp he
    have hend := hposition_arc_endpoint a e.1 e.2 he0.1.1 hx
    rcases hend with h | h
    · exact he0.2.1 h.symm
    · exact he0.2.2 h.symm
  obtain ⟨rF0, hrF0, hballF0⟩ :=
    (Metric.isOpen_iff.mp hAcompact.isClosed.isOpen_compl) (D.position a) hxA
  have hballF : Metric.ball (D.position a) rF0 ⊆ Aᶜ := hballF0
  have hrF0pos : 0 < rF0 := hrF0
  let r : Real := min rN (min rF0 1) / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrNlt : r < rN := by dsimp [r]; have := min_le_left rN (min rF0 1); linarith
  have hrFlt : r < rF0 := by
    dsimp [r]
    have hmin := min_le_right rN (min rF0 1)
    have hmin2 := min_le_left rF0 1
    linarith
  have hrlt1 : r < 1 := by
    dsimp [r]
    have hmin := min_le_right rN (min rF0 1)
    have hmin2 := min_le_right rF0 1
    linarith
  have hr_local (c : ι) (hc : P.plane.adjacent a c) : r < localEps c hc := by
    have hcS : c ∈ SN := (Set.Finite.mem_toFinset hNfin).mpr hc
    have hsmall := hrNsmall c hcS
    simpa [eps, hc] using hrNlt.trans hsmall
  have hforeign (c d : ι) (hcd : P.plane.adjacent c d)
      (hca : c ≠ a) (hda : d ≠ a) :
      Disjoint (D.edgeArc c d) (Metric.ball (D.position a) r) := RadialStarProof.hforeign ι P D a
          hadj_contact rN rF0 hballF hrFlt hrlt1 c d hcd hca hda
  have hu_injective : ∀ c d, P.plane.adjacent a c → P.plane.adjacent a d →
      u c = u d → c = d := RadialStarProof.hu_injective ι P D a hadj_contact hlocal rN u_norm
          localRay rF0 hr hr_local
  have vertexArc (v w : ι) (hvw : P.plane.adjacent v w) :
      D.position v ∈ D.edgeArc v w := by
    obtain ⟨g, _, _, hrange, hg0, _, _⟩ :=
      D.edgeArc_parameterization v w (hadj_contact v w hvw)
    rw [← hrange, ← hg0]
    exact ⟨⟨0, by norm_num⟩, rfl⟩
  have vertexRay (v : ι) (hvball : D.position v ∈ Metric.ball (D.position a) r) :
      ∃ c, P.plane.adjacent a c ∧ ∃ t : Real, 0 ≤ t ∧
        D.position v = D.position a + t • u c := RadialStarProof.vertexRay ι P D a  hlocal rN
            localRay rF0 hr hr_local hforeign vertexArc v hvball
  refine ⟨r, hr, u, u_norm, hu_injective, ?_, hforeign, ?_⟩
  · intro c hac
    exact localRay c hac r hr (hr_local c hac)
  · ext p
    constructor
    · rintro ⟨hpTrace, hpBall⟩
      rcases hpTrace with ⟨v, hvp⟩ | ⟨c, d, hcd, hpArc⟩
      · have hvball : D.position v ∈ Metric.ball (D.position a) r := hvp ▸ hpBall
        obtain ⟨c, hac, t, ht, hpos⟩ := vertexRay v hvball
        refine ⟨hpBall, c, hac, t, ht, ?_⟩
        exact hvp.symm.trans hpos
      · by_cases hca : c = a
        · subst c
          have hI : p ∈ D.edgeArc a d ∩ Metric.ball (D.position a) r := ⟨hpArc, hpBall⟩
          rw [localRay d hcd r hr (hr_local d hcd)] at hI
          rcases hI.2 with ⟨t, ht, hp⟩
          exact ⟨hpBall, d, hcd, t, ht, hp⟩
        · by_cases hda : d = a
          · subst d
            have had : P.plane.adjacent a c := (P.plane.adjacent_symmetric c a).mp hcd
            have hI : p ∈ D.edgeArc a c ∩ Metric.ball (D.position a) r := by
              have hs : D.edgeArc c a = D.edgeArc a c := D.edgeArc_symmetric c a
              simpa [hs] using And.intro hpArc hpBall
            rw [localRay c had r hr (hr_local c had)] at hI
            rcases hI.2 with ⟨t, ht, hp⟩
            exact ⟨hpBall, c, had, t, ht, hp⟩
          · have hfalse := (Set.disjoint_left.mp (hforeign c d hcd hca hda)) hpArc hpBall
            exact False.elim hfalse
    · rintro ⟨hpBall, c, hac, t, ht, hp⟩
      have hrayBall : D.position a + t • u c ∈ Metric.ball (D.position a) r := by
        rw [← hp]
        exact hpBall
      have hI : D.position a + t • u c ∈
          D.edgeArc a c ∩ Metric.ball (D.position a) r := by
        rw [localRay c hac r hr (hr_local c hac)]
        exact ⟨hrayBall, ⟨t, ht, rfl⟩⟩
      have hpArc : p ∈ D.edgeArc a c := by rw [hp]; exact hI.1
      exact ⟨Or.inr ⟨a, c, hac, hpArc⟩, hpBall⟩

end ApollonianSuperharmonic

end
