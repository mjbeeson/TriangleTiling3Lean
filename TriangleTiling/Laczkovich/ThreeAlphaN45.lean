/-
`theorem:N45` for M. Beeson, *Triangle tiling: the case 3α + 2β = π* (arXiv 1206.2229v4): an
isosceles triangle with base angles `α + β` can be `N`-tiled only if `N ≥ 45`.

Statement not yet checked by Beeson. The proof is the hand proof: with the tile
`(pq, q² - p², q²)`, the legs `M(p + q)q` carry `≥ q` edges `b` (one leg) and `≥ 2` edges `c`, the
base `Mp(p + q)` carries `≥ 2` edges `c`, and `N(q - p) = M²(q + p)` (`n45_arith`).
-/
import TriangleTiling.ThreeAlpha.N45Arith
import TriangleTiling.ThreeAlpha.DMatrix
import TriangleTiling.Laczkovich.ThreeAlphaIsoAB2
import TriangleTiling.Laczkovich.ThreeAlphaNo28
import TriangleTiling.Laczkovich.ThreeAlphaIsoExist
import TriangleTiling.Isosceles.NotSquarefree
import TriangleTiling.RightTile.Helper3
import TriangleTiling.Laczkovich.ThreeAlphaTriquadratic
import Erdos634.Draft.BeesonCor6

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.BeesonColoring EuclideanGeometry Set

variable {N : ℕ} (D : CongruentDissection N)

/-- An edge of length `b` (resp. `c`) is opposite the tile's `β` (resp. `γ`). -/
theorem edgeType_of_len {α β a b c : ℝ} (h : D.model.ThreeAlphaData α β a b c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (e : Fin N × Fin 3) :
    (dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b → edgeType D β e) ∧
    (dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = c → edgeType D (2 * α + β) e) := by
  obtain ⟨ρ, h0, l0, h1, l1, h2, l2⟩ := tile_threeAlpha D h e.1
  have hd : dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
      (D.tile e.1).oppLen (e.2 + 2) := by
    unfold Tri.oppLen
    rw [(by decide : ∀ x : Fin 3, x + 2 + 1 = x) e.2, (by decide : ∀ x : Fin 3, x + 2 + 2 = x + 1) e.2]
  have hloc : (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = (D.tile e.1).angleAt (e.2 + 2) :=
    Tri.localAngle_vertex _ _
  obtain ⟨x, hx⟩ := ρ.surjective (e.2 + 2)
  have hcase : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  unfold edgeType
  rw [hloc, hd, ← hx]
  refine ⟨fun hb => ?_, fun hc => ?_⟩
  · rcases hcase x with rfl | rfl | rfl
    · exact absurd (l0.symm.trans hb) hab
    · exact h1
    · exact absurd (l2.symm.trans hb) hbc.symm
  · rcases hcase x with rfl | rfl | rfl
    · exact absurd (l0.symm.trans hc) hac
    · exact absurd (l1.symm.trans hc) hbc
    · exact h2

open Classical in
/-- Two distinct tiles with `c` edges on side `j`: `d(j, γ) ≥ 2`. -/
theorem two_le_dEntry {α β a b c : ℝ} (h : D.model.ThreeAlphaData α β a b c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (j : Fin 3) {i i' : Fin N} (hii : i ≠ i')
    {m m' : Fin 3}
    (hm : (D.tile i).edge m ⊆ segment ℝ (D.target.pts (j + 1)) (D.target.pts (j + 2)))
    (hlm : dist ((D.tile i).pts m) ((D.tile i).pts (m + 1)) = c)
    (hm' : (D.tile i').edge m' ⊆ segment ℝ (D.target.pts (j + 1)) (D.target.pts (j + 2)))
    (hlm' : dist ((D.tile i').pts m') ((D.tile i').pts (m' + 1)) = c) :
    2 ≤ dEntry D j (2 * α + β) := by
  unfold dEntry
  apply Finset.one_lt_card.mpr
  refine ⟨(i, m), ?_, (i', m'), ?_, fun he => hii (congrArg Prod.fst he)⟩
  · simp only [Finset.mem_filter, sideEdges, Finset.mem_univ, true_and]
    exact ⟨hm, (edgeType_of_len D h hab hac hbc (i, m)).2 hlm⟩
  · simp only [Finset.mem_filter, sideEdges, Finset.mem_univ, true_and]
    exact ⟨hm', (edgeType_of_len D h hab hac hbc (i', m')).2 hlm'⟩

/-- Lemma 8 (`twocs`) on every side of the isosceles triangle with base angles `α + β`: if the side
is not a single `c` edge, it has at least two `c` edges. -/
theorem twocs_iso {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hirr : IrrPi α)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D)
    (hshape : D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + β)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (j : Fin 3) (hlen : D.target.oppLen j ≠ c) :
    2 ≤ dEntry D j (2 * α + β) := by
  obtain ⟨hα, hβ, hγ, -⟩ := model_facts D hrel hT
  have h := threeAlphaData_of_sides D hrel hT
  have hT' : Erdos634.Draft.LaczFormal.TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT; exact ⟨σ, h0, h1, h2⟩
  have hns3 := not_triple3 D hrel hT' hns
  have hπ := Real.pi_pos
  -- at most one `α` and one `β` at each corner
  have hcnt : ∀ k : Fin 3, anglesAt D k α ≤ 1 ∧ anglesAt D k β ≤ 1 := by
    intro k
    have hv : ∀ x, 0 < x → x < Real.pi → vcount D k x = anglesAt D k x := fun x h0 h1 =>
      vcount_eq_anglesAt D k h0.ne' h1.ne (by linarith)
    rw [← hv α hα (by linarith), ← hv β hβ (by linarith)]
    rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) k with rfl | rfl | rfl
    · obtain ⟨e1, e2, -⟩ := corner_counts D hirr hrel h hns3 0 (p := 1) (q := 1)
        (by rw [hshape.1]; push_cast; ring)
      omega
    · obtain ⟨e1, e2, -⟩ := corner_counts D hirr hrel h hns3 1 (p := 1) (q := 0)
        (by rw [hshape.2.1]; push_cast; ring)
      omega
    · obtain ⟨e1, e2, -⟩ := corner_counts D hirr hrel h hns3 2 (p := 1) (q := 1)
        (by rw [hshape.2.2]; push_cast; ring)
      omega
  obtain ⟨σ, hσ0, hσ2⟩ : ∃ σ : Equiv.Perm (Fin 3), σ 0 = j + 1 ∧ σ 2 = j + 2 :=
    (by decide : ∀ j : Fin 3, ∃ σ : Equiv.Perm (Fin 3), σ 0 = j + 1 ∧ σ 2 = j + 2) j
  set D' := relabelTarget D σ
  have e0 : D'.target.pts 0 = D.target.pts (j + 1) := by show D.target.pts (σ 0) = _; rw [hσ0]
  have e2 : D'.target.pts 2 = D.target.pts (j + 2) := by show D.target.pts (σ 2) = _; rw [hσ2]
  have hlt : ∀ k, D'.target.angleAt k < γ := by
    intro k
    rw [relabel_angleAt, hγ]
    rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) (σ k) with h' | h' | h' <;> rw [h']
    · rw [hshape.1]; linarith
    · rw [hshape.2.1]; linarith
    · rw [hshape.2.2]; linarith
  obtain ⟨i, i', hii, ⟨m, hm, hlm⟩, ⟨m', hm', hlm'⟩⟩ := twocs D' hT (by rw [hγ]; linarith)
    (irr_ratio hrel hα hβ hirr) hlt
    (Or.inr ⟨(hcnt (σ 0)).1, (hcnt (σ 0)).2, (hcnt (σ 2)).1, (hcnt (σ 2)).2⟩)
    (by rw [e0, e2]; exact hlen)
  rw [e0, e2] at hm hm'
  exact two_le_dEntry D h hab hac hbc j hii hm hlm hm' hlm'

/-- The angle at `B` between points on `BA` and `BC` is the angle `ABC`. -/
theorem apex_angle {A B C P Q : Plane} (hP : P ∈ segment ℝ A B) (hPB : P ≠ B)
    (hQ : Q ∈ segment ℝ B C) (hQB : Q ≠ B) : ∠ P B Q = ∠ A B C := by
  rw [(mem_segment_iff_wbtw.mp hP).symm.angle_eq_left _ hPB,
    (mem_segment_iff_wbtw.mp hQ).angle_eq_right _ hQB]

theorem fin3_edges : ∀ j₁ j₂ k : Fin 3, (k = j₁ ∨ k = j₁ + 1) → (k = j₂ ∨ k = j₂ + 1) → j₁ ≠ j₂ →
    (j₂ + 2 = j₁ ∨ j₂ + 2 = j₁ + 1) ∧ (j₁ + 2 = j₂ ∨ j₁ + 2 = j₂ + 1) ∧ j₂ + 2 ≠ k ∧
      j₁ + 2 ≠ k ∧ j₁ + 2 ≠ j₂ + 2 := by decide

open Classical in
/-- **A `b` edge at `B`.** The tile at `B` has its `α` there and its edges along `BA` and `BC`;
one of them is its `b` edge. -/
theorem b_edge_at_B {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hirr : IrrPi α)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D)
    (hshape : D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + β) :
    1 ≤ dEntry D 2 β ∨ 1 ≤ dEntry D 0 β := by
  obtain ⟨hα, hβ, hγ, -⟩ := model_facts D hrel hT
  have h := threeAlphaData_of_sides D hrel hT
  have hT' : Erdos634.Draft.LaczFormal.TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT; exact ⟨σ, h0, h1, h2⟩
  have hns3 := not_triple3 D hrel hT' hns
  have hπ := Real.pi_pos
  obtain ⟨-, -, hB1⟩ := corner_counts D hirr hrel h hns3 1 (p := 1) (q := 0)
    (by rw [hshape.2.1]; push_cast; ring)
  set B := D.target.pts 1
  obtain ⟨part₀, hcov₀, -, -⟩ := D.toDissection.side_walk 0
  obtain ⟨part₁, hcov₁, -, -⟩ := D.toDissection.side_walk 1
  have hcov₀' : (⋃ e ∈ part₀, (D.tile e.1).edge e.2) = segment ℝ (D.target.pts 0) B := hcov₀
  have hcov₁' : (⋃ e ∈ part₁, (D.tile e.1).edge e.2) = segment ℝ B (D.target.pts 2) := hcov₁
  obtain ⟨e₁, he₁, hend₁⟩ := side_edge_at_end D hcov₀' (V := B) (Or.inr rfl)
  obtain ⟨e₂, he₂, hend₂⟩ := side_edge_at_end D hcov₁' (V := B) (Or.inl rfl)
  have hsub₁ : (D.tile e₁.1).edge e₁.2 ⊆ segment ℝ (D.target.pts 0) B := by
    rw [← hcov₀']; intro y hy; exact Set.mem_iUnion₂.mpr ⟨e₁, he₁, hy⟩
  have hsub₂ : (D.tile e₂.1).edge e₂.2 ⊆ segment ℝ B (D.target.pts 2) := by
    rw [← hcov₁']; intro y hy; exact Set.mem_iUnion₂.mpr ⟨e₂, he₂, hy⟩
  -- one tile at `B`
  have hsame : e₁.1 = e₂.1 := by
    have hat : ∀ e : Fin N × Fin 3, ((D.tile e.1).pts e.2 = B ∨ (D.tile e.1).pts (e.2 + 1) = B) →
        e.1 ∈ (Finset.univ.filter fun i => TileAt D 1 i) := by
      intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases he with h' | h'
      · exact ⟨_, h'⟩
      · exact ⟨_, h'⟩
    have hc1 : (Finset.univ.filter fun i => TileAt D 1 i).card ≤ 1 := by
      have : tilesAt D 1 = (Finset.univ.filter fun i => TileAt D 1 i).card := by
        unfold tilesAt; congr
      omega
    exact Finset.card_le_one.mp hc1 _ (hat e₁ hend₁) _ (hat e₂ hend₂)
  set t := D.tile e₁.1
  rw [← hsame] at hend₂ hsub₂
  -- the vertex `kB` of `t` at `B`
  obtain ⟨kB, hkB, hk₁⟩ : ∃ kB, t.pts kB = B ∧ (kB = e₁.2 ∨ kB = e₁.2 + 1) := by
    rcases hend₁ with h' | h'
    · exact ⟨_, h', Or.inl rfl⟩
    · exact ⟨_, h', Or.inr rfl⟩
  have hk₂ : kB = e₂.2 ∨ kB = e₂.2 + 1 := by
    rcases hend₂ with h' | h'
    · exact Or.inl (t.indep.injective (hkB.trans h'.symm))
    · exact Or.inr (t.indep.injective (hkB.trans h'.symm))
  have hABC : ∠ (D.target.pts 0) B (D.target.pts 2) = α := by
    rw [angle_comm]; exact hshape.2.1
  -- the edges differ: otherwise their other endpoint would be on `BA` and `BC`
  have hne : e₁.2 ≠ e₂.2 := by
    intro heq
    obtain ⟨x, hx, hxk⟩ : ∃ x, (x = e₁.2 ∨ x = e₁.2 + 1) ∧ x ≠ kB := by
      rcases hk₁ with h' | h'
      · exact ⟨e₁.2 + 1, Or.inr rfl, by rw [h']; exact (fin3_ne_add_one _).symm⟩
      · exact ⟨e₁.2, Or.inl rfl, by rw [h']; exact fin3_ne_add_one _⟩
    have hxe : t.pts x ∈ t.edge e₁.2 := by
      rcases hx with rfl | rfl
      · exact left_mem_segment _ _ _
      · exact right_mem_segment _ _ _
    have hxB : t.pts x ≠ B := fun h' => hxk (t.indep.injective (h'.trans hkB.symm))
    have h1 := hsub₁ hxe
    have h2 := hsub₂ (heq ▸ hxe)
    have := apex_angle h1 hxB h2 hxB
    rw [angle_self_of_ne hxB, hABC] at this
    linarith
  obtain ⟨o₁, o₂, n₂, n₁, n₁₂⟩ := fin3_edges e₁.2 e₂.2 kB hk₁ hk₂ hne
  -- `P = t.pts (e₂.2 + 2)` is on `BA`, `Q = t.pts (e₁.2 + 2)` on `BC`
  have hP : t.pts (e₂.2 + 2) ∈ t.edge e₁.2 := by
    rcases o₁ with h' | h' <;> rw [h']
    · exact left_mem_segment _ _ _
    · exact right_mem_segment _ _ _
  have hQ : t.pts (e₁.2 + 2) ∈ t.edge e₂.2 := by
    rcases o₂ with h' | h' <;> rw [h']
    · exact left_mem_segment _ _ _
    · exact right_mem_segment _ _ _
  have hPB : t.pts (e₂.2 + 2) ≠ B := fun h' => n₂ (t.indep.injective (h'.trans hkB.symm))
  have hQB : t.pts (e₁.2 + 2) ≠ B := fun h' => n₁ (t.indep.injective (h'.trans hkB.symm))
  -- the angle of `t` at `kB` is `α`
  have hangk : t.angleAt kB = α := by
    have hc := corner_eq_of_two t kB (e₂.2 + 2) (e₁.2 + 2) n₂ n₁ n₁₂.symm
    rw [hkB, apex_angle (hsub₁ hP) hPB (hsub₂ hQ) hQB, hABC] at hc
    show cornerAngle (t.pts (kB + 1)) (t.pts kB) (t.pts (kB + 2)) = α
    rw [hkB]; exact hc
  obtain ⟨ρ, h0, -, h1, -, h2, -⟩ := tile_threeAlpha D h e₁.1
  have hkρ : kB = ρ 0 := by
    obtain ⟨x, hx⟩ := ρ.surjective kB
    rw [← hx] at hangk ⊢
    rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) x with rfl | rfl | rfl
    · rfl
    · rw [h1] at hangk
      exact absurd ⟨1 / 5, by push_cast; linarith⟩ hirr
    · rw [h2] at hangk; linarith
  -- one of the two third vertices is `ρ 1`
  have hthird : e₁.2 + 2 = ρ 1 ∨ e₂.2 + 2 = ρ 1 := by
    obtain ⟨x, hx⟩ := ρ.surjective (e₁.2 + 2)
    obtain ⟨y, hy⟩ := ρ.surjective (e₂.2 + 2)
    rw [hkρ, ← hx] at n₁
    rw [hkρ, ← hy] at n₂
    rw [← hx, ← hy] at n₁₂
    rw [← hx, ← hy]
    rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) x with rfl | rfl | rfl
    · exact absurd rfl n₁
    · exact Or.inl rfl
    · rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) y with rfl | rfl | rfl
      · exact absurd rfl n₂
      · exact Or.inr rfl
      · exact absurd rfl n₁₂
  have hloc : ∀ k, t.localAngle (t.pts k) = t.angleAt k := fun k => Tri.localAngle_vertex _ _
  rcases hthird with h' | h'
  · left
    unfold dEntry
    apply Finset.card_pos.mpr
    refine ⟨e₁, ?_⟩
    simp only [Finset.mem_filter, sideEdges, Finset.mem_univ, true_and]
    refine ⟨hsub₁, ?_⟩
    unfold edgeType; rw [hloc, h']; exact h1
  · right
    unfold dEntry
    apply Finset.card_pos.mpr
    refine ⟨(e₁.1, e₂.2), ?_⟩
    simp only [Finset.mem_filter, sideEdges, Finset.mem_univ, true_and]
    refine ⟨hsub₂, ?_⟩
    unfold edgeType; rw [hloc, h']; exact h1

/-- The base `Mp(p + r)` is not a single edge `c = r²`. -/
theorem base_ne_c (M p r : ℕ) (hp : 0 < p) (hpr : p < r) (hcop : Nat.Coprime p r) :
    M * p * (p + r) ≠ r * r := by
  intro h
  have hp1 : p = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.mul_right hcop hcop)
    ⟨M * (p + r), by rw [← h]; try ring⟩
  subst hp1
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 1 := ⟨r - 1, by omega⟩
  have h1 : t + 2 ∣ (t + 2) * t + 1 := ⟨M, by
    rw [show (t + 2) * t + 1 = (t + 1) * (t + 1) by ring, ← h]; ring⟩
  have h2 : t + 2 ∣ 1 := (Nat.dvd_add_right (dvd_mul_right _ _)).mp h1
  have := Nat.le_of_dvd one_pos h2
  omega


/-- The tiling equation `N(1 - s²) = Λ²`, `Λ = M(r + p)/r`, `s = p/r`, in `ℕ`. -/
theorem iso_N_eq (N M p r : ℕ) (hpr : p < r) (Λ : ℝ)
    (eN : (N : ℝ) = Λ ^ 2 / (1 - ((p : ℝ) / r) ^ 2)) (hΛ : Λ = M * (r + p) / r) :
    N * (r - p) = M ^ 2 * (r + p) := by
  have hpr' : (p : ℝ) < r := by exact_mod_cast hpr
  have hr : (0 : ℝ) < r := by linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  have hrp : (r : ℝ) - p ≠ 0 := by linarith
  have hrp' : (r : ℝ) + p ≠ 0 := by positivity
  have h1 : (1 : ℝ) - ((p : ℝ) / r) ^ 2 = (r - p) * (r + p) / r ^ 2 := by field_simp; ring
  rw [h1, hΛ] at eN
  have : (N : ℝ) * (r - p) = M ^ 2 * (r + p) := by
    rw [eN]; field_simp
  have h' : ((N * (r - p) : ℕ) : ℝ) = ((M ^ 2 * (r + p) : ℕ) : ℝ) := by
    push_cast [hpr.le]; linarith
  exact_mod_cast h'

/-- **Theorem `theorem:N45`.** Let isosceles triangle `ABC` with base angles `α + β` be `N`-tiled
by a triangle with angles `(α, β, γ)`, with `3α + 2β = π` and `α` not a rational multiple of `π`.
Then `N ≥ 45`. -/
theorem N45 {α β γ : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : Erdos634.Draft.LaczFormal.TileAngles D α β γ)
    (hA : D.target.angleAt 0 = α + β) (hC : D.target.angleAt 2 = α + β) (hirr : IrrPi α) :
    45 ≤ N := by
  have hπ := Real.pi_pos
  have hB : D.target.angleAt 1 = α := by have := D.target.angleAt_sum; linarith
  obtain ⟨σ, h0, h1, h2⟩ := hT
  have hTS : TileSides D α β γ (D.model.oppLen (σ 0)) (D.model.oppLen (σ 1)) (D.model.oppLen (σ 2)) :=
    ⟨σ, h0, h1, h2, rfl, rfl, rfl⟩
  set a₀ := D.model.oppLen (σ 0)
  set b₀ := D.model.oppLen (σ 1)
  set c₀ := D.model.oppLen (σ 2)
  have hns := not_similar_of_alpha_beta D hrel hTS hA
  obtain ⟨⟨q, hq⟩, -⟩ := rationaltile D hrel hTS hns
  obtain ⟨hα, hβ, hγ, -, hc₀, ha₀, hb₀, ht0, ht1, -⟩ := model_facts D hrel hTS
  set t := 2 * Real.cos (α + β)
  have hqt : (q : ℝ) = t := by rw [← hq, ha₀]; field_simp
  -- `q = p/r` in lowest terms
  have hq0 : (0 : ℝ) < q := by rw [hqt]; exact ht0
  have hq1 : (q : ℝ) < 1 := by rw [hqt]; exact ht1
  set p := q.num.toNat
  set r := q.den
  have hnum : (q.num : ℝ) = p := by
    have : 0 ≤ q.num := Rat.num_nonneg.mpr (by exact_mod_cast hq0.le)
    rw [show ((q.num.toNat : ℕ) : ℝ) = ((q.num.toNat : ℤ) : ℝ) by norm_cast, Int.toNat_of_nonneg this]
  have hqpr : (q : ℝ) = p / r := by rw [← hnum]; exact_mod_cast (Rat.num_div_den q).symm
  have hr : (0 : ℝ) < r := by exact_mod_cast q.den_pos
  have hp : 0 < p := by
    have : (0 : ℝ) < p := by rw [hqpr] at hq0; exact (div_pos_iff_of_pos_right hr).mp hq0
    exact_mod_cast this
  have hpr : p < r := by
    have : (p : ℝ) < r := by rw [hqpr, div_lt_one hr] at hq1; exact hq1
    exact_mod_cast this
  have hcop : Nat.Coprime p r := by
    have h0' : 0 ≤ q.num := Rat.num_nonneg.mpr (by exact_mod_cast hq0.le)
    have e : q.num.toNat = q.num.natAbs := by omega
    rw [show p = q.num.toNat from rfl, e]; exact q.reduced
  obtain ⟨hA0, hB0, hh0, hgcd⟩ := Erdos634.BeesonCor6.coprime_tile p r hp hpr hcop
  -- rescale to the integer tile `(pr, r² - p², r²)`
  have hle : p * p ≤ r * r := Nat.mul_le_mul hpr.le hpr.le
  have hBr : (((r * r - p * p : ℕ) : ℝ)) = (r : ℝ) * r - p * p := by push_cast [hle]; ring
  set κ := c₀ / ((r * r : ℕ) : ℝ)
  have hκ : 0 < κ := div_pos hc₀ (by positivity)
  have e1 : a₀ = κ * ((p * r : ℕ) : ℝ) := by
    rw [ha₀, ← hqt, hqpr]; simp only [κ]; push_cast; field_simp
  have e2 : b₀ = κ * ((r * r - p * p : ℕ) : ℝ) := by
    rw [hb₀, ← hqt, hqpr, hBr]; simp only [κ]; push_cast; field_simp
  have e3 : c₀ = κ * ((r * r : ℕ) : ℝ) := by simp only [κ]; field_simp
  rw [e1, e2, e3] at hTS
  obtain ⟨D₁, hT₁, hang⟩ := unscale hκ hTS
  have hsh : D₁.target.angleAt 0 = α + β ∧ D₁.target.angleAt 1 = α ∧ D₁.target.angleAt 2 = α + β :=
    ⟨by rw [hang, hA], by rw [hang, hB], by rw [hang, hC]⟩
  -- the colouring, with a black tile at `B` on `AB`
  have hns₁ := not_similar_of_alpha_beta D₁ hrel hT₁ hsh.1
  obtain ⟨i₀, hi₀⟩ := exists_atB_onAB D₁
  have hat : TileAt D₁ 1 i₀ := by obtain ⟨l, -, -, hl, -⟩ := hi₀; exact ⟨l, hl⟩
  have hTA₁ : Erdos634.Draft.LaczFormal.TileAngles D₁ α β γ := by
    obtain ⟨σ', h0', h1', h2', -⟩ := hT₁; exact ⟨σ', h0', h1', h2'⟩
  obtain ⟨ε, hε, hb1⟩ := signedtiles D₁ hrel hTA₁ hns₁ hat
  obtain ⟨eM, eN, eY, eZ, eX, -, -, hΛ⟩ := isoab_core D₁ hrel hT₁ hsh hε hi₀ hb1
  set Λ := Lam D₁
  set M : ℤ := ∑ i, ε i
  have hs : ((p * r : ℕ) : ℝ) / ((r * r : ℕ) : ℝ) = p / r := by push_cast; field_simp
  rw [hs] at eM eN eY
  have hMr : (M : ℝ) = Λ * r / (r + p) := by rw [eM]; field_simp
  have hMpos : 0 < M := by
    have : (0 : ℝ) < M := by rw [hMr]; positivity
    exact_mod_cast this
  set Mn := M.toNat
  have hMn : (Mn : ℝ) = M := by exact_mod_cast Int.toNat_of_nonneg hMpos.le
  have hMn0 : 0 < Mn := by omega
  have hΛM : Λ = Mn * (r + p) / r := by rw [hMn, hMr]; field_simp
  -- the three sides and the tiling equation, in `ℕ`
  have hX : ∀ j : Fin 3, j ≠ 1 → D₁.target.oppLen j = ((Mn * (p + r) * r : ℕ) : ℝ) := by
    intro j hj
    rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) j with rfl | rfl | rfl
    · rw [eX, hΛM]; push_cast; field_simp; ring
    · exact absurd rfl hj
    · rw [eZ, hΛM]; push_cast; field_simp; ring
  have hY : D₁.target.oppLen 1 = ((Mn * p * (p + r) : ℕ) : ℝ) := by
    rw [eY, hΛM]; push_cast; field_simp; ring
  have hN : N * (r - p) = Mn ^ 2 * (r + p) := iso_N_eq N Mn p r hpr Λ eN hΛM
  -- the `d` matrix rows
  have h₁ := threeAlphaData_of_sides D₁ hrel hT₁
  have hrow : ∀ j : Fin 3, ((D₁.target.oppLen j)) = ((dEntry D₁ j α * (p * r) +
      dEntry D₁ j β * (r * r - p * p) + dEntry D₁ j (2 * α + β) * (r * r) : ℕ) : ℝ) := by
    intro j
    rw [dmatrix_row D₁ hirr hrel h₁ j]; push_cast; ring
  have hrowN : ∀ j : Fin 3, ∀ L : ℕ, D₁.target.oppLen j = (L : ℝ) →
      L = dEntry D₁ j α * (p * r) + dEntry D₁ j β * (r * r - p * p) +
        dEntry D₁ j (2 * α + β) * (r * r) := by
    intro j L hL
    have := (hrow j).symm.trans hL
    exact_mod_cast this.symm
  -- the tile's sides are distinct
  have hab : ((p * r : ℕ) : ℝ) ≠ ((r * r - p * p : ℕ) : ℝ) := by
    intro h'
    have h'' : p * r = r * r - p * p := by exact_mod_cast h'
    apply base_ne_c 1 p r hp hpr hcop
    rw [show 1 * p * (p + r) = p * p + p * r by ring]; omega
  have hac : ((p * r : ℕ) : ℝ) ≠ ((r * r : ℕ) : ℝ) := by
    intro h'
    have h'' : p * r = r * r := by exact_mod_cast h'
    have := Nat.mul_lt_mul_of_pos_right hpr (by omega : 0 < r)
    omega
  have hbc : ((r * r - p * p : ℕ) : ℝ) ≠ ((r * r : ℕ) : ℝ) := by
    intro h'
    have h'' : r * r - p * p = r * r := by exact_mod_cast h'
    have := Nat.sub_lt (Nat.mul_pos (by omega : 0 < r) (by omega : 0 < r)) (Nat.mul_pos hp hp)
    omega
  -- two `c` edges on each side
  have hlegc : ((Mn * (p + r) * r : ℕ) : ℝ) ≠ ((r * r : ℕ) : ℝ) := by
    intro h'
    have h'' : Mn * (p + r) * r = r * r := by exact_mod_cast h'
    have : (p + r) * r ≤ Mn * (p + r) * r := by
      rw [mul_assoc]; exact Nat.le_mul_of_pos_left _ hMn0
    have : r * r < (p + r) * r := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    omega
  have hc0 := twocs_iso D₁ hrel hirr hT₁ hns₁ hsh hab hac hbc 0 (by rw [hX 0 (by decide)]; exact hlegc)
  have hc2 := twocs_iso D₁ hrel hirr hT₁ hns₁ hsh hab hac hbc 2 (by rw [hX 2 (by decide)]; exact hlegc)
  have hc1 := twocs_iso D₁ hrel hirr hT₁ hns₁ hsh hab hac hbc 1 (by
    rw [hY]; intro h'
    exact base_ne_c Mn p r hp hpr hcop (by exact_mod_cast h'))
  -- `r` divides the numbers of `b` edges on the legs
  obtain ⟨⟨hd2, hd0⟩, -⟩ := halfintegermu D₁ hrel hT₁ hsh ⟨rfl, rfl, rfl⟩ hgcd hε hi₀ hb1
  have hk : Nat.gcd (p * r) (r * r) = r := by
    rw [Nat.gcd_mul_right, hcop, one_mul]
  rw [hk] at hd2 hd0
  have hbase := hrowN 1 _ hY
  have hleg0 := hrowN 0 _ (hX 0 (by decide))
  have hleg2 := hrowN 2 _ (hX 2 (by decide))
  rcases b_edge_at_B D₁ hrel hirr hT₁ hns₁ hsh with hb | hb
  · exact n45_arith p r Mn N hp hpr hMn0 hN _ _ _ (by rw [hleg2])
      (Nat.le_of_dvd hb hd2) hc2 _ _ _ hbase hc1
  · exact n45_arith p r Mn N hp hpr hMn0 hN _ _ _ (by rw [hleg0])
      (Nat.le_of_dvd hb hd0) hc0 _ _ _ hbase hc1

end TriangleTiling.ThreeAlpha
