/-
`Φ₁`, `Φ₂` on a tiling (Section 5 of M. Beeson, *Triangle tiling: the case 3α + 2β = π*,
arXiv 1206.2229v4): edge directions of tiles (`lemma:deltadirections`, `lemma:Phitile`), the
integers `M₁`, `M₂` (`theorem:Mdef`), and the sign table `lemma:Phisigns`.

Here `α ∉ ℚπ` is a hypothesis (`lemma:angles`); the theorems named after the paper's labels are
in `TriangleTiling.Laczkovich.ThreeAlphaPhi`.

A tile's edges are indexed by the opposite vertex: `edir T v` is the direction of the edge
opposite vertex `v` (traversing `T` counterclockwise). Going around the tile, the direction turns
at each vertex by the exterior angle, `π - α = 2δ`, `π - β ≡ -3δ`, `π - γ = δ`.
-/
import TriangleTiling.ThreeAlpha.Phi
import TriangleTiling.ThreeAlpha.Coloring

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry Erdos634.BeesonColoring

/-- The direction of the edge of `T` opposite vertex `v`. -/
noncomputable def edir (T : Tri) (v : Fin 3) : Real.Angle := (T.leftUnit (v + 1)).angle

theorem leftUnit_eq_edir (T : Tri) (k : Fin 3) : (T.leftUnit k).angle = edir T (k + 2) := by
  unfold edir; congr 2; fin_cases k <;> rfl

/-- Turning at vertex `v`: from the edge opposite `v + 1` to the edge opposite `v + 2`, by `s`
times the exterior angle, `s = ±1` the orientation. -/
theorem turn (T : Tri) : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ v : Fin 3,
    edir T (v + 2) = edir T (v + 1) + ((s * (Real.pi - T.angleAt v) : ℝ) : Real.Angle) := by
  rcases T.det_pos_or_neg with hT | hT
  · refine ⟨1, Or.inl rfl, fun v => ?_⟩
    have h := T.leftUnit_turn_of_pos hT (v + 2)
    unfold edir
    rw [show v + 2 + 1 = v by fin_cases v <;> rfl, show v + 1 + 1 = v + 2 by fin_cases v <;> rfl]
    rw [show v + 2 + 1 = v by fin_cases v <;> rfl] at h
    rw [h]; push_cast; ring_nf
  · refine ⟨-1, Or.inr rfl, fun v => ?_⟩
    have h := T.leftUnit_turn_of_neg hT (v + 2)
    unfold edir
    rw [show v + 2 + 1 = v by fin_cases v <;> rfl, show v + 1 + 1 = v + 2 by fin_cases v <;> rfl]
    rw [show v + 2 + 1 = v by fin_cases v <;> rfl] at h
    rw [h]; push_cast
    rw [add_assoc, ← Real.Angle.coe_add]; ring_nf; simp

variable {α β a b c : ℝ}

/-- The exterior angles in terms of `δ = α + β`. -/
theorem ext_alpha (hrel : 3 * α + 2 * β = Real.pi) :
    ((Real.pi - α : ℝ) : Real.Angle) = ((2 * (α + β) : ℝ) : Real.Angle) := by
  congr 1; linarith

theorem ext_beta (hrel : 3 * α + 2 * β = Real.pi) :
    ((Real.pi - β : ℝ) : Real.Angle) = ((-3 * (α + β) : ℝ) : Real.Angle) := by
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub]
  exact ⟨1, by push_cast; linarith⟩

theorem ext_gamma (hrel : 3 * α + 2 * β = Real.pi) :
    ((Real.pi - (2 * α + β) : ℝ) : Real.Angle) = ((1 * (α + β) : ℝ) : Real.Angle) := by
  congr 1; linarith


theorem coe_shift {x θ₀ : Real.Angle} {r t : ℝ} (h : x = θ₀ + (r : Real.Angle)) :
    x + (t : Real.Angle) = θ₀ + ((r + t : ℝ) : Real.Angle) := by
  rw [h, add_assoc, ← Real.Angle.coe_add]

theorem coe_unshift {x y θ₀ : Real.Angle} {r t : ℝ} (h : y = x + (t : Real.Angle))
    (hy : y = θ₀ + (r : Real.Angle)) : x = θ₀ + ((r - t : ℝ) : Real.Angle) := by
  rw [Real.Angle.coe_sub, ← add_sub_assoc, ← hy, h, add_sub_cancel_right]

theorem coe_congr {θ₀ : Real.Angle} {r r' : ℝ} (h : r = r') :
    θ₀ + (r : Real.Angle) = θ₀ + (r' : Real.Angle) := by rw [h]

/-- **Edge directions of a tile.** If one edge of a tile `(α, β, γ)` has direction
`θ₀ + mδ + επ`, then its `a`, `b`, `c` edges have directions `θ₀ + nδ + επ`,
`θ₀ + (n + ρ)δ + επ`, `θ₀ + (n + 3ρ)δ + επ` for some `n` and `ρ = ±1`. -/
theorem tile_dirs (hrel : 3 * α + 2 * β = Real.pi) (hαβ : α ≠ β) {T : Tri}
    (hT : T.ThreeAlphaData α β a b c)
    (θ₀ : Real.Angle) {v₀ : Fin 3} {m e : ℤ}
    (h₀ : edir T v₀ = θ₀ + ((m * (α + β) + e * Real.pi : ℝ) : Real.Angle)) :
    ∃ n ρ : ℤ, (ρ = 1 ∨ ρ = -1) ∧ ∀ v : Fin 3,
      (T.angleAt v = α → edir T v = θ₀ + ((n * (α + β) + e * Real.pi : ℝ) : Real.Angle)) ∧
      (T.angleAt v = β → edir T v = θ₀ + (((n + ρ) * (α + β) + e * Real.pi : ℝ) : Real.Angle)) ∧
      (T.angleAt v = 2 * α + β →
        edir T v = θ₀ + (((n + 3 * ρ) * (α + β) + e * Real.pi : ℝ) : Real.Angle)) := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := hT
  obtain ⟨-, -, -, hα, hβ⟩ := model_abc_pos (T := T) ⟨σ, h0, rfl, h1, rfl, h2, rfl⟩
  obtain ⟨s, hs, ht⟩ := turn T
  set δ := α + β with hδ
  -- The turns, `s` times the exterior angles, as multiples of `δ`.
  have tA : ((s * (Real.pi - α) : ℝ) : Real.Angle) = (((2 * s : ℤ) * δ : ℝ) : Real.Angle) := by
    congr 1; push_cast; rw [hδ]; linear_combination (-(s : ℝ)) * hrel
  have tB : ((s * (Real.pi - β) : ℝ) : Real.Angle) = (((-3 * s : ℤ) * δ : ℝ) : Real.Angle) := by
    rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub]
    exact ⟨s, by push_cast; rw [hδ]; linear_combination (s : ℝ) * hrel⟩
  have tC : ((s * (Real.pi - (2 * α + β)) : ℝ) : Real.Angle) = (((s : ℤ) * δ : ℝ) : Real.Angle) := by
    congr 1; push_cast; rw [hδ]; linear_combination (-(s : ℝ)) * hrel
  set A := σ 0
  set B := σ 1
  set C := σ 2
  have hAB : A ≠ B := σ.injective.ne (by decide)
  have hAC : A ≠ C := σ.injective.ne (by decide)
  have hBC : B ≠ C := σ.injective.ne (by decide)
  have f11 : ∀ x : Fin 3, x + 1 + 1 = x + 2 := by decide
  have f12 : ∀ x : Fin 3, x + 1 + 2 = x := by decide
  have f21 : ∀ x : Fin 3, x + 2 + 1 = x := by decide
  have f22 : ∀ x : Fin 3, x + 2 + 2 = x + 1 := by decide
  have three : ∀ x y z w : Fin 3, x ≠ y → x ≠ z → y ≠ z → w = x ∨ w = y ∨ w = z := by decide
  have hcase : (B = A + 1 ∧ C = A + 2) ∨ (B = A + 2 ∧ C = A + 1) := by
    revert hAB hAC hBC; generalize A = x; generalize B = y; generalize C = z; revert x y z
    decide
  -- In both cases: `edir B = edir A + ρδ`, `edir C = edir A + 3ρδ`.
  obtain ⟨ρ, hρ, eB, eC⟩ : ∃ ρ : ℤ, (ρ = 1 ∨ ρ = -1) ∧
      edir T B = edir T A + (((ρ : ℝ) * δ : ℝ) : Real.Angle) ∧
      edir T C = edir T A + (((3 * ρ : ℤ) : ℝ) * δ : Real.Angle) := by
    rcases hcase with ⟨hB, hC⟩ | ⟨hB, hC⟩
    · have hC' := ht C
      rw [show C + 2 = B by rw [hC, f22, hB], show C + 1 = A by rw [hC, f21], h2, tC] at hC'
      have hA' := ht A
      rw [show A + 2 = C from hC.symm, show A + 1 = B from hB.symm, h0, tA, hC'] at hA'
      refine ⟨s, hs, hC', ?_⟩
      rw [hA', add_assoc, ← Real.Angle.coe_add]; congr 2; push_cast; ring
    · have hC' := ht C
      rw [show C + 2 = A by rw [hC, f12], show C + 1 = B by rw [hC, f11, hB], h2, tC] at hC'
      have hB' := ht B
      rw [show B + 2 = C by rw [hB, f22, hC], show B + 1 = A by rw [hB, f21], h1, tB] at hB'
      refine ⟨-s, by rcases hs with h | h <;> simp [h], ?_, ?_⟩
      · rw [hC', add_assoc, ← Real.Angle.coe_add]; push_cast; ring_nf; simp
      · rw [hB']; push_cast; ring_nf
  -- `edir A` from the given edge.
  obtain ⟨n, eA⟩ : ∃ n : ℤ, edir T A = θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle) := by
    have hv : v₀ = A ∨ v₀ = B ∨ v₀ = C := three A B C v₀ hAB hAC hBC
    rcases hv with rfl | rfl | rfl
    · exact ⟨m, h₀⟩
    · refine ⟨m - ρ, ?_⟩
      rw [coe_unshift eB h₀]; apply coe_congr; push_cast; ring
    · refine ⟨m - 3 * ρ, ?_⟩
      rw [coe_unshift eC h₀]; apply coe_congr; push_cast; ring
  refine ⟨n, ρ, hρ, fun v => ⟨fun hv => ?_, fun hv => ?_, fun hv => ?_⟩⟩
  · have : v = A := by
      by_contra hne
      have hv' : v = B ∨ v = C := (three A B C v hAB hAC hBC).resolve_left hne
      rcases hv' with rfl | rfl
      · exact hαβ (hv.symm.trans h1)
      · rw [h2] at hv; linarith
    rw [this, eA]
  · have : v = B := by
      by_contra hne
      have hv' : v = A ∨ v = C := by
        rcases three A B C v hAB hAC hBC with h | h | h
        · exact Or.inl h
        · exact absurd h hne
        · exact Or.inr h
      rcases hv' with rfl | rfl
      · exact hαβ (h0.symm.trans hv)
      · rw [h2] at hv; linarith
    rw [this, eB, coe_shift eA]; apply coe_congr; push_cast; ring
  · have : v = C := by
      by_contra hne
      have hv' : v = A ∨ v = B := by
        rcases three A B C v hAB hAC hBC with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hne
      rcases hv' with rfl | rfl
      · rw [h0] at hv; linarith
      · rw [h1] at hv; linarith
    rw [this, eC, coe_shift eA]; apply coe_congr; push_cast; ring

theorem delta_irr' (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi) : ¬ ∃ q : ℚ, α + β = (q : ℝ) * Real.pi := by
  rintro ⟨q, hq⟩
  exact hirr ⟨1 - 2 * q, by push_cast; linarith⟩

/-- Reduce `ε` to `{0, 1}`. -/
theorem coset_norm (θ₀ : Real.Angle) (n e : ℤ) :
    θ₀ + ((n * (α + β) + e * Real.pi : ℝ) : Real.Angle)
      = θ₀ + ((n * (α + β) + ((e % 2 : ℤ) : ℝ) * Real.pi : ℝ) : Real.Angle) := by
  congr 1
  have he : e = (e % 2) + (e / 2 + e / 2) := by omega
  conv_lhs => rw [he]
  push_cast
  rw [show (n : ℝ) * (α + β) + (((e % 2 : ℤ) : ℝ) + ((e / 2 : ℤ) + (e / 2 : ℤ))) * Real.pi
      = (n * (α + β) + ((e % 2 : ℤ) : ℝ) * Real.pi) + ((e / 2 + e / 2 : ℤ) : ℝ) * Real.pi by
    push_cast; ring]
  exact coe_add_two_pi_mul' _ _

theorem emod_two_cases (e : ℤ) : e % 2 = 0 ∨ e % 2 = 1 := by omega

/-- The value of `Φ` on a tile, from the directions of its edges opposite each vertex. -/
theorem PhiR_eq (Φ : Real.Angle → ℝ) (T : Tri) :
    PhiR Φ T = ∑ v : Fin 3, T.oppLen v * Φ (edir T v) := by
  unfold PhiR Tri.flux edir Tri.oppLen
  have e01 : (0 : Fin 3) + 1 = 1 := rfl
  have e02 : (0 : Fin 3) + 2 = 2 := rfl
  have e11 : (1 : Fin 3) + 1 = 2 := rfl
  have e12 : (1 : Fin 3) + 2 = 0 := rfl
  have e21 : (2 : Fin 3) + 1 = 0 := rfl
  have e22 : (2 : Fin 3) + 2 = 1 := rfl
  simp only [Fin.sum_univ_three, smul_eq_mul, e01, e02, e11, e12, e21, e22]
  ring

section Tiling

variable {N : ℕ} (D : CongruentDissection N) (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
  (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c)
include hirr hrel h

theorem alpha_ne_beta : α ≠ β := fun e => hirr ⟨1 / 5, by push_cast; linarith⟩

/-- All three edges of a tile are in the coset, once one is. -/
theorem all_edges (i : Fin N) {v₀ : Fin 3} {m e : ℤ}
    (h₀ : edir (D.tile i) v₀ = baseDir D + ((m * (α + β) + e * Real.pi : ℝ) : Real.Angle)) :
    ∀ k : Fin 3, ∃ n : ℤ,
      ((D.tile i).leftUnit k).angle = baseDir D + ((n * (α + β) + e * Real.pi : ℝ) : Real.Angle) := by
  obtain ⟨n, ρ, -, hv⟩ := tile_dirs hrel (alpha_ne_beta D hirr hrel h) (tile_threeAlpha D h i) _ h₀
  intro k
  rw [leftUnit_eq_edir]
  rcases tile_angle_mem D h i (k + 2) with e1 | e1 | e1
  · exact ⟨n, (hv _).1 e1⟩
  · exact ⟨n + ρ, by rw [(hv _).2.1 e1]; push_cast; rfl⟩
  · exact ⟨n + 3 * ρ, by rw [(hv _).2.2 e1]; push_cast; rfl⟩

/-- **Every edge direction of the tiling is `θ₀ + nδ + επ`**, `θ₀` the direction of `AB`. -/
theorem edges_in_coset (i : Fin N) (k : Fin 3) :
    ∃ n e : ℤ, ((D.tile i).leftUnit k).angle
      = baseDir D + ((n * (α + β) + e * Real.pi : ℝ) : Real.Angle) := by
  classical
  -- A tile with an edge on `AB`.
  obtain ⟨⟨i₀, k₀⟩, hmem⟩ : (D.toDissection.sideEdges 0).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hsum := D.toDissection.side_len_sum 0
    rw [hne, Finset.sum_empty] at hsum
    have : D.target.pts 0 ≠ D.target.pts (0 + 1) := fun e =>
      absurd (D.target.indep.injective e) (by decide)
    exact this (dist_eq_zero.mp hsum.symm)
  have hsub : D.toDissection.eSet (i₀, k₀) ⊆ D.target.edge 0 := by
    unfold Dissection.sideEdges at hmem
    exact (Finset.mem_filter.mp hmem).2
  have hdir : ((D.tile i₀).leftUnit k₀).angle = baseDir D := by
    have := D.toDissection.eDir_of_side hsub
    unfold baseDir
    exact congrArg Dir.angle this
  -- Propagate along the adjacency graph.
  have hP : ∀ j, Relation.ReflTransGen (fun a b => D.toDissection.Adj a b) i₀ j →
      ∀ k : Fin 3, ∃ n e : ℤ, ((D.tile j).leftUnit k).angle
        = baseDir D + ((n * (α + β) + e * Real.pi : ℝ) : Real.Angle) := by
    intro j hj
    induction hj with
    | refl =>
      have h₀ : edir (D.tile i₀) (k₀ + 2)
          = baseDir D + ((((0 : ℤ) : ℝ) * (α + β) + ((0 : ℤ) : ℝ) * Real.pi : ℝ) : Real.Angle) := by
        rw [← leftUnit_eq_edir, hdir]; simp
      intro k
      obtain ⟨n, hn⟩ := all_edges D hirr hrel h i₀ h₀ k
      exact ⟨n, 0, hn⟩
    | @tail j₁ c' _ hbc ih =>
      obtain ⟨k, l, hkl⟩ := hbc.leftUnit_neg
      obtain ⟨n, e, hn⟩ := ih k
      have h₀ : edir (D.tile c') (l + 2)
          = baseDir D + ((n * (α + β) + ((e + 1 : ℤ) : ℝ) * Real.pi : ℝ) : Real.Angle) := by
        rw [← leftUnit_eq_edir]
        have : ((D.tile c').leftUnit l).angle = ((D.tile j₁).leftUnit k).angle + Real.pi := by
          rw [show (D.tile c').leftUnit l = Dir.neg ((D.tile j₁).leftUnit k) from hkl, Dir.angle_neg]
        rw [this, hn, add_assoc, ← Real.Angle.coe_add]; push_cast; ring_nf
      intro k'
      obtain ⟨n', hn'⟩ := all_edges D hirr hrel h c' h₀ k'
      exact ⟨n', e + 1, hn'⟩
  exact hP i (D.toDissection.adjConnected i₀ i) k

theorem delta_irr : ¬ ∃ q : ℚ, α + β = (q : ℝ) * Real.pi := by
  rintro ⟨q, hq⟩
  exact hirr ⟨1 - 2 * q, by push_cast; linarith⟩

/-- `lemma:Phitile`, with `α ∉ ℚπ`. -/
theorem Phitile_irr (i : Fin N) :
    ∃ n ε ρ : ℤ, (ε = 0 ∨ ε = 1) ∧ (ρ = 1 ∨ ρ = -1) ∧
      (∀ k : Fin 3,
        ((D.tile i).angleAt (k + 2) = α → ((D.tile i).leftUnit k).angle
          = baseDir D + ((n * (α + β) + ε * Real.pi : ℝ) : Real.Angle)) ∧
        ((D.tile i).angleAt (k + 2) = β → ((D.tile i).leftUnit k).angle
          = baseDir D + (((n + ρ) * (α + β) + ε * Real.pi : ℝ) : Real.Angle)) ∧
        ((D.tile i).angleAt (k + 2) = 2 * α + β → ((D.tile i).leftUnit k).angle
          = baseDir D + (((n + 3 * ρ) * (α + β) + ε * Real.pi : ℝ) : Real.Angle))) ∧
      PhiR (Phi1 (α + β) (baseDir D)) (D.tile i) = (ε.negOnePow : ℤ) * (a + b + c) ∧
      PhiR (Phi2 (α + β) (baseDir D)) (D.tile i) = ((n + ε).negOnePow : ℤ) * (a - b - c) ∧
      |PhiR (Phi1 (α + β) (baseDir D)) (D.tile i)| = a + b + c ∧
      |PhiR (Phi2 (α + β) (baseDir D)) (D.tile i)| = b + c - a := by
  have hδ := delta_irr D hirr hrel h
  obtain ⟨m, e, hme⟩ := edges_in_coset D hirr hrel h i 0
  rw [coset_norm] at hme
  set ε := e % 2 with hε
  have h₀ : edir (D.tile i) (0 + 2) = baseDir D + ((m * (α + β) + ε * Real.pi : ℝ) : Real.Angle) := by
    rw [← leftUnit_eq_edir, hme]
  obtain ⟨n, ρ, hρ, hv⟩ :=
    tile_dirs hrel (alpha_ne_beta D hirr hrel h) (tile_threeAlpha D h i) _ h₀
  have hT := tile_threeAlpha D h i
  obtain ⟨σ, h0, l0, h1, l1, h2, l2⟩ := hT
  obtain ⟨ha, hb, hc, -, -⟩ := model_abc_pos h
  have hsum : ∀ (f : Fin 3 → ℝ), ∑ v, f v = f (σ 0) + f (σ 1) + f (σ 2) := by
    intro f
    rw [← Equiv.sum_comp σ f, Fin.sum_univ_three]
  have hr : ((n + ρ + ε).negOnePow : ℤ) = - ((n + ε).negOnePow : ℤ) ∧
      ((n + 3 * ρ + ε).negOnePow : ℤ) = - ((n + ε).negOnePow : ℤ) := by
    rcases hρ with rfl | rfl
    · rw [show n + 1 + ε = (n + ε) + 1 by ring, show n + 3 * 1 + ε = (n + ε) + 1 + 2 by ring,
        Int.negOnePow_add (n + ε + 1) 2, Int.negOnePow_succ]
      simp [show (2 : ℤ).negOnePow = 1 by decide]
    · rw [show n + -1 + ε = (n + ε) + 1 - 2 by ring, show n + 3 * -1 + ε = (n + ε) + 1 - 4 by ring,
        Int.negOnePow_sub, Int.negOnePow_sub, Int.negOnePow_succ]
      simp [show (2 : ℤ).negOnePow = 1 by decide, show (4 : ℤ).negOnePow = 1 by decide]
  have c1 : ((n : ℝ) + ρ) = ((n + ρ : ℤ) : ℝ) := by push_cast; ring
  have c3 : ((n : ℝ) + 3 * ρ) = ((n + 3 * ρ : ℤ) : ℝ) := by push_cast; ring
  have hP1 : PhiR (Phi1 (α + β) (baseDir D)) (D.tile i) = (ε.negOnePow : ℤ) * (a + b + c) := by
    rw [PhiR_eq, hsum, (hv _).1 h0, (hv _).2.1 h1, (hv _).2.2 h2, c1, c3, phi1_eval hδ,
      phi1_eval hδ, phi1_eval hδ, l0, l1, l2]
    ring
  have hP2 : PhiR (Phi2 (α + β) (baseDir D)) (D.tile i) = ((n + ε).negOnePow : ℤ) * (a - b - c) := by
    rw [PhiR_eq, hsum, (hv _).1 h0, (hv _).2.1 h1, (hv _).2.2 h2, c1, c3, phi2_eval hδ,
      phi2_eval hδ, phi2_eval hδ, l0, l1, l2, hr.1, hr.2]
    push_cast
    ring
  have hlt : a < b + c := by
    have := (D.tile i).oppLen_lt (σ 0)
    have e3 : ∀ x : Fin 3, x ≠ σ 0 → x = σ 1 ∨ x = σ 2 := by
      intro x hx
      obtain ⟨y, rfl⟩ := σ.surjective x
      have : y = 0 ∨ y = 1 ∨ y = 2 := by fin_cases y <;> simp
      rcases this with rfl | rfl | rfl
      · exact absurd rfl hx
      · exact Or.inl rfl
      · exact Or.inr rfl
    have n1 : σ 0 + 1 ≠ σ 0 := (by decide : ∀ x : Fin 3, x + 1 ≠ x) _
    have n2 : σ 0 + 2 ≠ σ 0 := (by decide : ∀ x : Fin 3, x + 2 ≠ x) _
    have n12 : σ 0 + 1 ≠ σ 0 + 2 := (by decide : ∀ x : Fin 3, x + 1 ≠ x + 2) _
    rcases e3 _ n1 with e | e <;> rcases e3 _ n2 with f | f
    · exact absurd (e.trans f.symm) n12
    · rw [l0, e, f, l1, l2] at this; linarith
    · rw [l0, e, f, l1, l2] at this; linarith
    · exact absurd (e.trans f.symm) n12
  refine ⟨n, ε, ρ, emod_two_cases e, hρ, fun k => ⟨fun hk => ?_, fun hk => ?_, fun hk => ?_⟩,
    hP1, hP2, ?_, ?_⟩
  · rw [leftUnit_eq_edir]; exact (hv _).1 hk
  · rw [leftUnit_eq_edir]; exact (hv _).2.1 hk
  · rw [leftUnit_eq_edir]; exact (hv _).2.2 hk
  · have h1' : |((ε.negOnePow : ℤ) : ℝ)| = 1 := by rw [← Int.cast_abs, Int.abs_negOnePow]; simp
    rw [hP1, abs_mul, h1', one_mul, abs_of_pos (by linarith)]
  · have h1' : |(((n + ε).negOnePow : ℤ) : ℝ)| = 1 := by
      rw [← Int.cast_abs, Int.abs_negOnePow]; simp
    rw [hP2, abs_mul, h1', one_mul, abs_of_neg (by linarith)]
    ring

/-- `theorem:Mdef`, with `α ∉ ℚπ`. -/
theorem Mdef_irr :
    ∃ n ε : Fin N → ℤ,
      (∀ j, (ε j = 0 ∨ ε j = 1) ∧
        PhiR (Phi1 (α + β) (baseDir D)) (D.tile j) = ((ε j).negOnePow : ℤ) * (a + b + c) ∧
        PhiR (Phi2 (α + β) (baseDir D)) (D.tile j)
          = ((n j + ε j).negOnePow : ℤ) * (a - b - c)) ∧
      ∃ M₁ M₂ : ℤ, M₁ = ∑ j, ((ε j).negOnePow : ℤ) ∧ M₂ = ∑ j, ((n j + ε j).negOnePow : ℤ) ∧
        |M₁| ≤ N ∧ |M₂| ≤ N ∧ M₁ ≡ N [ZMOD 2] ∧ M₂ ≡ N [ZMOD 2] ∧
        PhiR (Phi1 (α + β) (baseDir D)) D.target = M₁ * (a + b + c) ∧
        PhiR (Phi2 (α + β) (baseDir D)) D.target = M₂ * (a - b - c) := by
  have hδ := delta_irr D hirr hrel h
  choose n ε ρ hε _ _ hP1 hP2 _ _ using fun j => Phitile_irr D hirr hrel h j
  have habs : ∀ u : Fin N → ℤ, |∑ j, ((u j).negOnePow : ℤ)| ≤ N := by
    intro u
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simp [Int.abs_negOnePow]
  have hmod : ∀ u : Fin N → ℤ, ∑ j, ((u j).negOnePow : ℤ) ≡ N [ZMOD 2] := by
    intro u
    rw [Int.modEq_iff_dvd]
    have hN : (N : ℤ) = ∑ _j : Fin N, (1 : ℤ) := by simp
    rw [hN, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun j _ => ?_
    rcases Int.units_eq_one_or (u j).negOnePow with e | e <;> rw [e] <;> decide
  obtain ⟨c1, c2⟩ := Phicancellation D hδ (baseDir D)
  refine ⟨n, ε, fun j => ⟨hε j, hP1 j, hP2 j⟩, _, _, rfl, rfl, habs ε, habs (fun j => n j + ε j),
    hmod ε, hmod (fun j => n j + ε j), ?_, ?_⟩
  · rw [c1, Finset.sum_congr rfl fun j _ => hP1 j, ← Finset.sum_mul]; push_cast; rfl
  · rw [c2, Finset.sum_congr rfl fun j _ => hP2 j, ← Finset.sum_mul]; push_cast; rfl

/-- The `ε` of a tile, read off from its `Φ₁`-value, is the `ε` of each of its edges. -/
theorem eps_of_edge {i : Fin N} {e' : ℤ} (he' : e' = 0 ∨ e' = 1)
    (hP : PhiR (Phi1 (α + β) (baseDir D)) (D.tile i) = ((e'.negOnePow : ℤ) : ℝ) * (a + b + c))
    {k : Fin 3} {m f : ℤ}
    (hk : ((D.tile i).leftUnit k).angle = baseDir D + ((m * (α + β) + f * Real.pi : ℝ) : Real.Angle)) :
    Even (f - e') := by
  have hδ := delta_irr D hirr hrel h
  obtain ⟨n, ε, ρ, hε, -, hdir, hP1, -⟩ := Phitile_irr D hirr hrel h i
  obtain ⟨ha, hb, hc, -, -⟩ := model_abc_pos h
  have hpos : (a + b + c) ≠ 0 := by linarith
  have he : e' = ε := by
    rw [hP1] at hP
    have := mul_right_cancel₀ hpos hP
    have := (Int.cast_inj (α := ℝ)).mp this
    rcases hε with rfl | rfl <;> rcases he' with rfl | rfl <;> first | rfl | (exfalso; revert this; decide)
  subst he
  rcases tile_angle_mem D h i (k + 2) with e1 | e1 | e1
  · exact (coset_eq hδ (hk.symm.trans ((hdir k).1 e1))).2
  · have := (hdir k).2.1 e1
    rw [show ((n : ℝ) + ρ) = ((n + ρ : ℤ) : ℝ) by push_cast; ring] at this
    exact (coset_eq hδ (hk.symm.trans this)).2
  · have := (hdir k).2.2 e1
    rw [show ((n : ℝ) + 3 * ρ) = ((n + 3 * ρ : ℤ) : ℝ) by push_cast; ring] at this
    exact (coset_eq hδ (hk.symm.trans this)).2

/-- `remark:Phi1iscoloring`, with `α ∉ ℚπ`. -/
theorem Phi1iscoloring_irr {ε : Fin N → ℤ}
    (hε : ∀ j, (ε j = 0 ∨ ε j = 1) ∧
      PhiR (Phi1 (α + β) (baseDir D)) (D.tile j) = ((ε j).negOnePow : ℤ) * (a + b + c)) :
    D.toDissection.ProperColouring (fun j => ((ε j).negOnePow : ℤ)) ∧
      ∀ i, AtBOnAB D i → ε i = 0 := by
  refine ⟨⟨fun i => ?_, fun i j hij => ?_⟩, fun i hi => ?_⟩
  · rcases Int.units_eq_one_or (ε i).negOnePow with e | e <;> simp [e]
  · obtain ⟨k, l, hkl⟩ := hij.leftUnit_neg
    obtain ⟨m, f, hm⟩ := edges_in_coset D hirr hrel h i k
    have hj : ((D.tile j).leftUnit l).angle
        = baseDir D + ((m * (α + β) + ((f + 1 : ℤ) : ℝ) * Real.pi : ℝ) : Real.Angle) := by
      have : ((D.tile j).leftUnit l).angle = ((D.tile i).leftUnit k).angle + Real.pi := by
        rw [show (D.tile j).leftUnit l = Dir.neg ((D.tile i).leftUnit k) from hkl, Dir.angle_neg]
      rw [this, hm, add_assoc, ← Real.Angle.coe_add]; push_cast; ring_nf
    have e1 := eps_of_edge D hirr hrel h (hε i).1 (hε i).2 hm
    have e2 := eps_of_edge D hirr hrel h (hε j).1 (hε j).2 hj
    show ((ε i).negOnePow : ℤ) = -((ε j).negOnePow : ℤ)
    obtain ⟨r, hr⟩ := e1
    obtain ⟨r', hr'⟩ := e2
    rcases (hε i).1 with h1 | h1 <;> rcases (hε j).1 with h2 | h2 <;> rw [h1, h2] <;>
      rw [h1] at hr <;> rw [h2] at hr' <;> first | decide | omega
  · obtain ⟨e, he⟩ := edge_of_AtBOnAB D hi
    have hdir : ((D.tile i).leftUnit e).angle
        = baseDir D + ((((0 : ℤ) : ℝ) * (α + β) + ((0 : ℤ) : ℝ) * Real.pi : ℝ) : Real.Angle) := by
      have := D.toDissection.eDir_of_side (e := (i, e)) he
      simp only [Int.cast_zero, zero_mul, add_zero, Real.Angle.coe_zero]
      unfold baseDir
      exact congrArg Dir.angle this
    have := eps_of_edge D hirr hrel h (hε i).1 (hε i).2 hdir
    rcases (hε i).1 with h1 | h1
    · exact h1
    · rw [h1] at this; exact absurd this (by decide)

omit hirr h in
/-- An exterior angle `π - (pα + qβ)` in `δ`-coordinates. -/
theorem ext_coords (p q : ℤ) :
    Real.pi - (p * α + q * β) = (2 * p - 3 * q : ℤ) * (α + β) + (1 - p + q : ℤ) * Real.pi := by
  push_cast
  linear_combination ((q : ℝ) - p) * hrel

omit h in
/-- One row of `lemma:Phisigns`: the angles at `B` and `C` are `p₁α + q₁β` and `p₂α + q₂β`. -/
theorem Phisigns_row (hccw : 0 < D.target.det) (p₁ q₁ p₂ q₂ : ℤ)
    (h₁ : D.target.angleAt 1 = p₁ * α + q₁ * β) (h₂ : D.target.angleAt 2 = p₂ * α + q₂ * β)
    {u₁ u₂ v₁ v₂ : ℤ} (hu₁ : ((1 - p₁ + q₁).negOnePow : ℤ) = u₁)
    (hu₂ : (((1 - p₁ + q₁) + (1 - p₂ + q₂)).negOnePow : ℤ) = u₂)
    (hv₁ : (((2 * p₁ - 3 * q₁) + (1 - p₁ + q₁)).negOnePow : ℤ) = v₁)
    (hv₂ : (((2 * p₁ - 3 * q₁) + (2 * p₂ - 3 * q₂) + ((1 - p₁ + q₁) + (1 - p₂ + q₂))).negOnePow
      : ℤ) = v₂) :
    Phi1 (α + β) (baseDir D) (D.target.leftUnit 1).angle = u₁ ∧
      Phi1 (α + β) (baseDir D) (D.target.leftUnit 2).angle = u₂ ∧
      Phi2 (α + β) (baseDir D) (D.target.leftUnit 1).angle = v₁ ∧
      Phi2 (α + β) (baseDir D) (D.target.leftUnit 2).angle = v₂ := by
  have hδ := delta_irr' hirr hrel
  have t0 := D.target.leftUnit_turn_of_pos hccw 0
  have t1 := D.target.leftUnit_turn_of_pos hccw 1
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (1 : Fin 3) + 1 = 2 from rfl] at t0 t1
  rw [h₁, ext_coords hrel] at t0
  rw [h₂, ext_coords hrel] at t1
  have eBC : (D.target.leftUnit 1).angle = baseDir D + ((((2 * p₁ - 3 * q₁ : ℤ) : ℝ) * (α + β)
      + ((1 - p₁ + q₁ : ℤ) : ℝ) * Real.pi : ℝ) : Real.Angle) := t0
  have eCA : (D.target.leftUnit 2).angle = baseDir D + (((((2 * p₁ - 3 * q₁) + (2 * p₂ - 3 * q₂) : ℤ)
      : ℝ) * (α + β) + (((1 - p₁ + q₁) + (1 - p₂ + q₂) : ℤ) : ℝ) * Real.pi : ℝ) : Real.Angle) := by
    rw [t1, eBC, add_assoc, ← Real.Angle.coe_add]; push_cast; ring_nf
  rw [eBC, eCA, phi1_eval hδ, phi1_eval hδ, phi2_eval hδ, phi2_eval hδ, hu₁, hu₂, hv₁, hv₂]
  exact ⟨rfl, rfl, rfl, rfl⟩

end Tiling

end TriangleTiling.ThreeAlpha
