/-
`lemma:baseangles` (Section 6 of M. Beeson, *Tilings of an isosceles triangle*): if an isosceles
triangle `ABC` is `N`-tiled by a tile with angles `(α, β, π/2)`, its base angles are `α` or `β`.

The paper derives this from Laczkovich's classification; here it follows from the two tables of
`Laczkovich.Tables`. With it, `theorem:isosceles2`, `lemma:notprime` and `theorem:whichABC`
(iv), (v) hold without the base-angle hypothesis of their `_of_baseangles` versions.

The proof does not need `ABC` to be non-equilateral: an equilateral triangle tiled by a
right-angled tile is tiled by the 30-60-90 triangle, and its angle `π/3` is a tile angle.
-/
import TriangleTiling.Laczkovich.Tables
import TriangleTiling.RightTile.WhichABC

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
open TriangleTiling.Laczkovich

variable {N : ℕ} (D : CongruentDissection N)

theorem model_angleAt_0 : D.model.angleAt 0 = tileα D := rfl
theorem model_angleAt_1 : D.model.angleAt 1 = tileβ D := rfl
theorem model_angleAt_2 : D.model.angleAt 2 = tileγ D := rfl
theorem target_angleAt_0 :
    D.target.angleAt 0 = ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) := rfl
theorem target_angleAt_2 :
    D.target.angleAt 2 = ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) :=
  angle_comm _ _ _

/-- A value of an unordered triple of tile angles is the tile's angle at some vertex, and every
tile angle is one of the three values. -/
theorem tileAngles_mem {x y z : ℝ} (h : TileAngles D x y z) (k : Fin 3) :
    D.model.angleAt k = x ∨ D.model.angleAt k = y ∨ D.model.angleAt k = z := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  have hk : k = σ (σ.symm k) := (σ.apply_symm_apply k).symm
  have : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  rcases this (σ.symm k) with h | h | h <;> rw [hk, h]
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h2)

theorem irr_false {α : ℝ} (hα : IrrPi α) (q : ℚ) (h : α = q * Real.pi) : False :=
  hα ⟨q, h⟩

/-- **Lemma `lemma:baseangles`.** If the isosceles triangle `ABC` (angles at `A` and `C` equal) is
`N`-tiled by a tile with a right angle `γ`, then its base angles are both `β` or both `α`. -/
theorem baseangles (hright : tileγ D = Real.pi / 2)
    (hiso : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) =
      ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0)) :
    (∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D ∧
        ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D) ∨
      (∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D ∧
        ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D) := by
  set θ := D.target.angleAt 0 with hθ
  have ht0 : D.target.angleAt 0 = θ := rfl
  have ht2 : D.target.angleAt 2 = θ := by rw [target_angleAt_2, ← hiso]; rfl
  have hpi := Real.pi_pos
  -- `θ < π/2`, since the apex angle is positive.
  have hθ2 : θ < Real.pi / 2 := by
    have hs := D.target.angleAt_sum
    have h1 := Erdos634.Geometry.CaseA.LemmaV.angle_pos D.target 1
    linarith
  have hm2 : D.model.angleAt 2 = Real.pi / 2 := hright
  -- It suffices that `θ` is the tile's angle at vertex `0` or `1`.
  suffices key : θ = D.model.angleAt 0 ∨ θ = D.model.angleAt 1 by
    have hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = θ := rfl
    rw [← hiso, hA]
    rcases key with h | h
    · exact Or.inr ⟨h, h⟩
    · exact Or.inl ⟨h, h⟩
  -- A tile angle equal to `θ` is not the right angle.
  have hidx : ∀ k : Fin 3, D.model.angleAt k = θ → θ = D.model.angleAt 0 ∨
      θ = D.model.angleAt 1 := by
    intro k hk
    have : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
    rcases this k with rfl | rfl | rfl
    · exact Or.inl hk.symm
    · exact Or.inr hk.symm
    · rw [hm2] at hk; linarith
  -- From `ABC` similar to the tile.
  have of_similar : SimilarTM D → θ = D.model.angleAt 0 ∨ θ = D.model.angleAt 1 := by
    rintro ⟨μ, τ, h⟩
    exact hidx (τ 0) (h 0).1.symm
  -- From the right-angle row: the doubled angle of `ABC` is `θ`.
  have of_right : RightRow D → θ = D.model.angleAt 0 ∨ θ = D.model.angleAt 1 := by
    rintro ⟨α, β, ⟨ρ, r0, -, -⟩, ⟨σ, s0, s1, -⟩⟩
    have hσ : σ 0 ≠ σ 1 := fun h => absurd (σ.injective h) (by decide)
    have hαθ : α = θ := by
      have : ∀ i j : Fin 3, i ≠ j → (i = 0 ∨ i = 2) ∨ (j = 0 ∨ j = 2) := by decide
      rcases this (σ 0) (σ 1) hσ with (h | h) | (h | h)
      · rw [← s0, h, ht0]
      · rw [← s0, h, ht2]
      · rw [← s1, h, ht0]
      · rw [← s1, h, ht2]
    exact hidx (ρ 0) (r0.trans hαθ)
  -- A triple of tile angles contains the right angle `π/2`.
  have has_right : ∀ {x y z : ℝ}, TileAngles D x y z →
      x = Real.pi / 2 ∨ y = Real.pi / 2 ∨ z = Real.pi / 2 := by
    intro x y z h
    rcases tileAngles_mem D h 2 with h | h | h <;> rw [hm2] at h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr h.symm)
  by_cases hall : ∀ k, ∃ q : ℚ, D.model.angleAt k = q * Real.pi
  · rcases table_commensurable D hall with h | h | ⟨hT, -⟩
    · exact of_similar h
    · exact of_right h
    · exfalso
      rcases has_right hT with h | h | h <;> linarith
  · push Not at hall
    obtain ⟨k, hk⟩ := hall
    have hirr : ∃ k, IrrPi (D.model.angleAt k) := ⟨k, fun ⟨q, hq⟩ => hk q hq⟩
    rcases table_incommensurable D hirr with h | h | ⟨-, α, hα, hT⟩ | ⟨α, hα, hT, -⟩ |
        ⟨α, β, hα, hrel, hT, -⟩ | ⟨α, hα, hT, -⟩
    · exact of_similar h
    · exact of_right h
    · exfalso
      rcases has_right hT with h | h | h
      · exact irr_false hα (1 / 2) (by push_cast; linarith)
      · exact irr_false hα (1 / 6) (by push_cast; linarith)
      · linarith
    · exfalso
      rcases has_right hT with h | h | h
      · exact irr_false hα (1 / 2) (by push_cast; linarith)
      · exact irr_false hα (1 / 6) (by push_cast; linarith)
      · exact irr_false hα (1 / 4) (by push_cast; linarith)
    · exfalso
      rcases has_right hT with h | h | h
      · exact irr_false hα (1 / 2) (by push_cast; linarith)
      · exact irr_false hα 0 (by push_cast; linarith)
      · exact irr_false hα 0 (by push_cast; linarith)
    · exfalso
      rcases has_right hT with h | h | h
      · exact irr_false hα (1 / 2) (by push_cast; linarith)
      · exact irr_false hα (-1 / 6) (by push_cast; linarith)
      · linarith

/-- **Theorem `theorem:isosceles2`.** Let the isosceles triangle `ABC` (angles at `A` and `C`
equal) be `N`-tiled by a tile with angles `(α, β, π/2)`. Then (i) `N` is a square and
`α = β = π/4`, or (ii) `N` is twice a square, or (iii) `N = 6k²` and `β` or `α` is `π/6`, or
(iv) `N` is even, and `N` and `N/2` are sums of two squares. -/
theorem isosceles2 (hright : tileγ D = Real.pi / 2)
    (hiso : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) =
      ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0)) :
    ((∃ m : ℕ, N = m ^ 2) ∧ tileα D = Real.pi / 4 ∧ tileβ D = Real.pi / 4) ∨
    (∃ m : ℕ, N = 2 * m ^ 2) ∨
    ((∃ k : ℕ, N = 6 * k ^ 2) ∧ (tileβ D = Real.pi / 6 ∨ tileα D = Real.pi / 6)) ∨
    (Even N ∧ (∃ x y : ℕ, N = x ^ 2 + y ^ 2) ∧ ∃ x y : ℕ, N / 2 = x ^ 2 + y ^ 2) :=
  isosceles2_of_baseangles D hright (baseangles D hright hiso)

/-- **Corollary `lemma:notprime`.** If an isosceles triangle is `N`-tiled by a right triangle and
`N > 2`, then `N` is not prime, and `N` is not twice a prime `p ≡ 3 (mod 4)` unless `N = 6`. -/
theorem notprime (hright : tileγ D = Real.pi / 2)
    (hiso : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) =
      ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0))
    (hN2 : 2 < N) :
    ¬ N.Prime ∧ ∀ p : ℕ, p.Prime → p % 4 = 3 → N = 2 * p → N = 6 :=
  notprime_of_baseangles D hright (baseangles D hright hiso) hN2

/-- **`theorem:whichABC` (iv), "only if".** If `N = 6k²` (`k > 0`) and an isosceles triangle is
`N`-tiled by a right triangle, then the tile is the 30-60-90 triangle and `ABC` has base angles
`π/6`, or is equilateral. -/
theorem whichABC_iv (hright : tileγ D = Real.pi / 2)
    (hiso : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) =
      ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0))
    {k : ℕ} (hk : 0 < k) (hN : N = 6 * k ^ 2) :
    (tileβ D = Real.pi / 6 ∧ tileα D = Real.pi / 3) ∨
      (tileβ D = Real.pi / 3 ∧ tileα D = Real.pi / 6) :=
  whichABC_iv_of_baseangles D hright (baseangles D hright hiso) hk hN

/-- **`theorem:whichABC` (v).** Every `N`-tiling of an isosceles triangle by a right triangle falls
under one of the cases (i)–(iv). -/
theorem whichABC_v (hright : tileγ D = Real.pi / 2)
    (hiso : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) =
      ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0)) :
    (∃ m : ℕ, N = 2 * m ^ 2) ∨ (∃ x y : ℕ, N = 2 * (x ^ 2 + y ^ 2)) ∨
      ((∃ m : ℕ, N = m ^ 2) ∧ tileα D = Real.pi / 4 ∧ tileβ D = Real.pi / 4) ∨
      ∃ k : ℕ, N = 6 * k ^ 2 :=
  whichABC_v_of_baseangles D hright (baseangles D hright hiso)

end TriangleTiling
