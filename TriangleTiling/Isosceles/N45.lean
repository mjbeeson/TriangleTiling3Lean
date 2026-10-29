/-
`theorem:N45`, from Section 10 of M. Beeson, *Tilings of an isosceles triangle*: `N ≥ 45`.

The proof is the paper's (since its rewrite of October 2026, which replaced the finite search of
`lemma:boundarytilings`, `lemma:N/4`, `lemma:abcbound` and `lemma:no20`): on a side whose tile at `B` has its `α` there, `lemma:qandrnotzero` and the divisibility `k ∣ q` give
`t = p k + q' b + r m` with `q', r ≥ 1`, where `|AB| = k t` and `t² = N b`; for `N ≤ 44` this
forces `r = 1`, which `lemma:no28` rules out.

Conventions as in `TriangleTiling.Isosceles.AreaEquation`.
-/
import TriangleTiling.Isosceles.No28

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

set_option maxHeartbeats 2000000 in
/-- **The arithmetic of `theorem:N45`.** For the tile `(k², m² - k², km)` and a side relation
`X = p k² + q (m² - k²) + r km` with `q, r ≥ 1` and `X² = N k² (m² - k²)`, if `N ≤ 44` then
`r = 1`. -/
theorem N45_arith (N k m p q r X : ℕ) (hk : 0 < k) (hkm : k < m) (hm2k : m < 2 * k)
    (hcop : Nat.Coprime k m) (hX : X = p * k ^ 2 + q * (m ^ 2 - k ^ 2) + r * (k * m))
    (hX2 : X ^ 2 = N * k ^ 2 * (m ^ 2 - k ^ 2)) (hq : 1 ≤ q) (hr : 1 ≤ r) (hN : N ≤ 44) :
    r = 1 := by
  set b := m ^ 2 - k ^ 2 with hbdef
  have hk2m2 : k ^ 2 < m ^ 2 := Nat.pow_lt_pow_left hkm two_ne_zero
  have hbm : b + k ^ 2 = m ^ 2 := by omega
  -- `X = k t` with `t² = N b`.
  have hkX : k ∣ X := (Nat.pow_dvd_pow_iff two_ne_zero).mp ⟨N * b, by rw [hX2]; ring⟩
  obtain ⟨t, ht⟩ := hkX
  have ht2 : t ^ 2 = N * b := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < k ^ 2 by positivity)
    calc k ^ 2 * t ^ 2 = X ^ 2 := by rw [ht]; ring
      _ = k ^ 2 * (N * b) := by rw [hX2]; ring
  -- `k ∣ q`, so `q = k q'`.
  have hkq : k ∣ q := by
    have h1 : k ∣ q * b := by
      have h2 : k ∣ X := ⟨t, ht⟩
      rw [hX, show p * k ^ 2 + q * b + r * (k * m) = (p * k ^ 2 + r * (k * m)) + q * b by ring]
        at h2
      exact (Nat.dvd_add_right ⟨p * k + r * m, by ring⟩).mp h2
    have h3 : k ∣ q * m ^ 2 := by
      rw [← hbm, mul_add]
      exact Nat.dvd_add h1 ⟨q * k, by ring⟩
    exact (Nat.Coprime.pow_right 2 hcop).dvd_of_dvd_mul_right h3
  obtain ⟨q', rfl⟩ := hkq
  have hq' : 1 ≤ q' := by
    rcases Nat.eq_zero_or_pos q' with h | h
    · rw [h] at hq; simp at hq
    · exact h
  have htk : t = p * k + q' * b + r * m := by
    apply Nat.eq_of_mul_eq_mul_left hk
    rw [← ht, hX]; ring
  -- If `r ≥ 2`, then `(b + 2m)² ≤ t² = N b ≤ 44 b`, leaving a few cases.
  by_contra hr1
  have hr2 : 2 ≤ r := by omega
  have htlow : b + 2 * m ≤ t := by
    rw [htk]
    have : b ≤ q' * b := Nat.le_mul_of_pos_left b hq'
    have : 2 * m ≤ r * m := Nat.mul_le_mul_right m hr2
    omega
  have hNb : t ^ 2 ≤ 44 * b := by rw [ht2]; exact Nat.mul_le_mul_right b hN
  have h1 : (b + 2 * m) ^ 2 ≤ 44 * b := (Nat.pow_le_pow_left htlow 2).trans hNb
  have hk6 : k ≤ 6 := by
    have h2 : 2 * k + 1 ≤ b := by
      have : (k + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hkm 2
      nlinarith
    nlinarith
  have hm12 : m ≤ 12 := by omega
  have ht44 : t ≤ 44 := by
    have hb : b ≤ 44 := by nlinarith
    nlinarith
  interval_cases k <;> interval_cases m <;> simp only [hbdef] at htlow hNb ht2 <;>
    norm_num at htlow hNb ht2 hm2k hkm <;>
    (try omega) <;> interval_cases t <;> omega

/-- **The mirror image** of a tiling: the same tiles, with `A` and `C` swapped. -/
noncomputable def swapAC {N : ℕ} (D : CongruentDissection N) : CongruentDissection N where
  target := ⟨![D.target.pts 2, D.target.pts 1, D.target.pts 0], by
    have h := tri_indep D.target
    have : ![D.target.pts 2, D.target.pts 1, D.target.pts 0] =
        ![D.target.pts 0, D.target.pts 1, D.target.pts 2] ∘ (Equiv.swap (0 : Fin 3) 2) := by
      ext i; fin_cases i <;> rfl
    rw [this]
    exact h.comp_embedding (Equiv.swap (0 : Fin 3) 2).toEmbedding⟩
  tile := D.tile
  covers := by
    rw [D.covers]
    show convexHull ℝ (Set.range D.target.pts) =
      convexHull ℝ (Set.range ![D.target.pts 2, D.target.pts 1, D.target.pts 0])
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact ⟨2, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact ⟨2, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
  interiors_disjoint := D.interiors_disjoint
  model := D.model
  tiles_congruent := D.tiles_congruent

/-- `theorem:N45` on one side: if the tile at `B` supported by `AB` has its `α` at `B`, then
`N ≥ 45`. -/
theorem N45_side {N : ℕ} (D : CongruentDissection N) {a b c : ℕ}
    (ha : dist (D.model.pts 1) (D.model.pts 2) = a)
    (hb : dist (D.model.pts 2) (D.model.pts 0) = b)
    (hc : dist (D.model.pts 0) (D.model.pts 1) = c)
    (hcop : Nat.gcd (Nat.gcd a b) c = 1) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D)
    (part : Finset (Fin N × Fin 3))
    (hcov : (⋃ e ∈ part, (D.tile e.1).edge e.2) =
      segment ℝ (D.target.pts 0) (D.target.pts 1))
    (hdisj : ∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ →
      ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton)
    (hsum : ∑ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
      = dist (D.target.pts 0) (D.target.pts 1))
    (hB : ∀ e ∈ part, ((D.tile e.1).pts e.2 = D.target.pts 1 ∨
      (D.tile e.1).pts (e.2 + 1) = D.target.pts 1) →
        (D.tile e.1).localAngle (D.target.pts 1) = tileα D) :
    45 ≤ N := by
  classical
  by_contra hN
  push Not at hN
  obtain ⟨-, -, hX2⟩ := areaequation_core D ha hb hc rfl rfl hγ hA hC
  have hw := side_walk_counts D hγ hirr part _ hsum
  rw [ha, hb, hc] at hw
  obtain ⟨⟨eq, hq, hqβ⟩, ⟨er, hr, hrγ⟩⟩ := qandrnotzero D hγ hirr hA hC part hcov hdisj hB
  have hno := no28 D ha hb hc hcop hγ hirr hA hC part hcov hdisj hB
  set p := (part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
    = tileα D).card
  set q := (part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
    = tileβ D).card
  set r := (part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
    = tileγ D).card
  have hq1 : 1 ≤ q := Finset.card_pos.mpr ⟨eq, Finset.mem_filter.mpr ⟨hq, hqβ⟩⟩
  have hr1 : 1 ≤ r := Finset.card_pos.mpr ⟨er, Finset.mem_filter.mpr ⟨hr, hrγ⟩⟩
  -- The tile `(k², m² - k², km)`.
  have hcab : c ^ 2 = a ^ 2 + a * b := by
    have := (twoalphatiles (tri_indep D.model) ha hb hc).mp hγ
    exact_mod_cast this
  obtain ⟨n1, n2, n3⟩ := strict_triangle_ineqs (tri_indep D.model)
  rw [ha, hb, hc] at n1 n2 n3
  have n1' : a < b + c := by exact_mod_cast n1
  have n2' : b < c + a := by exact_mod_cast n2
  have n3' : c < a + b := by exact_mod_cast n3
  obtain ⟨k, m, hkm_cop, hkm, hm2k, hak, hbk, hck⟩ :=
    (luthar a b c).mp ⟨hcop, hcab, n1', by omega, n3'⟩
  have hk0 : 0 < k := by omega
  -- `|AB|` is the integer `p a + q b + r c`.
  set Xn := p * a + q * b + r * c with hXn
  have hXr : dist (D.target.pts 0) (D.target.pts 1) = (Xn : ℝ) := by rw [hw, hXn]; push_cast; ring
  rw [hXr] at hX2
  have hX2n : Xn ^ 2 = N * a * b := by exact_mod_cast hX2
  rw [hak, hbk, hck] at hXn
  rw [hak, hbk] at hX2n
  exact hno (N45_arith N k m p q r Xn hk0 hkm hm2k hkm_cop hXn
    (by rw [hX2n]) hq1 hr1 (by omega))

/-- **Theorem `theorem:N45`, for a tile with integer sides** (the general form is `N45`). Let the
isosceles triangle `ABC` with base angles `α` (`α` not a rational multiple of `π`) be `N`-tiled by
a triangle with angles `(α, β, 2α)` and integer sides without common factor. Then `N ≥ 45`.

The proof is the paper's: see the module docstring. The side used
is `AB` or `BC`, whichever has its tile at `B` with the `α` there (`beta_at_apex`); for `BC` the
argument runs on the mirror image `swapAC`. -/
theorem N45_int {N : ℕ} (D : CongruentDissection N) {a b c : ℕ}
    (ha : dist (D.model.pts 1) (D.model.pts 2) = a)
    (hb : dist (D.model.pts 2) (D.model.pts 0) = b)
    (hc : dist (D.model.pts 0) (D.model.pts 1) = c)
    (hcop : Nat.gcd (Nat.gcd a b) c = 1) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D) :
    45 ≤ N := by
  classical
  obtain ⟨part₀, hcov₀, hdisj₀, hsum₀⟩ := D.toDissection.side_walk 0
  obtain ⟨part₁, hcov₁, hdisj₁, hsum₁⟩ := D.toDissection.side_walk 1
  have h01 : (0 : Fin 3) + 1 = 1 := rfl
  have h12 : (1 : Fin 3) + 1 = 2 := rfl
  rw [h01] at hcov₀ hsum₀
  rw [h12] at hcov₁ hsum₁
  obtain ⟨-, -, -, -, -, cγB, -, -⟩ := counts_at_corners D hγ hirr hA hC
  -- A tile at `B` without its `β` there has its `α` there.
  have hα : ∀ (i : Fin N) (j : Fin 3), (D.tile i).pts j = D.target.pts 1 →
      (D.tile i).localAngle (D.target.pts 1) ≠ tileβ D →
        (D.tile i).localAngle (D.target.pts 1) = tileα D := by
    intro i j hj hβ
    rcases localAngle_at_own_vertex_mem' D i j with h | h | h <;> rw [hj] at h
    · exact h
    · exact absurd h hβ
    · exact absurd h (ne_of_angleCount_zero D cγB i)
  have hvert : ∀ e : Fin N × Fin 3, ((D.tile e.1).pts e.2 = D.target.pts 1 ∨
      (D.tile e.1).pts (e.2 + 1) = D.target.pts 1) →
        ∃ j : Fin 3, (D.tile e.1).pts j = D.target.pts 1 := by
    intro e h
    rcases h with h | h
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  rcases beta_at_apex D hγ hirr hA hC part₀ part₁ hcov₀ hcov₁ with hB | hB
  · refine N45_side D ha hb hc hcop hγ hirr hA hC part₀ hcov₀ hdisj₀ hsum₀ ?_
    intro e he hend
    obtain ⟨j, hj⟩ := hvert e hend
    exact hα e.1 j hj (hB e he hend)
  · -- Side `BC`, on the mirror image.
    refine N45_side (swapAC D) ha hb hc hcop hγ hirr hC hA part₁ ?_ hdisj₁ ?_ ?_
    · show (⋃ e ∈ part₁, (D.tile e.1).edge e.2) = segment ℝ (D.target.pts 2) (D.target.pts 1)
      exact hcov₁.trans (segment_symm ℝ _ _)
    · show _ = dist (D.target.pts 2) (D.target.pts 1)
      exact hsum₁.trans (dist_comm _ _)
    · intro e he hend
      obtain ⟨j, hj⟩ := hvert e hend
      exact hα e.1 j hj (hB e he hend)

end TriangleTiling
