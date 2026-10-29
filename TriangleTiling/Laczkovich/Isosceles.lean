/-
`theorem:laczkovich-isosceles` (Section 3 of M. Beeson, *Tilings of an isosceles triangle*):
Table `isosceles`, the possible tiles of an isosceles, non-equilateral triangle, specialized from
Laczkovich's two tables (`Laczkovich.Tables`).
-/
import TriangleTiling.Laczkovich.BaseAngles

namespace TriangleTiling.Laczkovich

open Erdos634.Geometry EuclideanGeometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles TileAngles.swap)

variable {N : ℕ} (D : CongruentDissection N)

/-- In an isosceles triangle two of any listing of its angles are equal. -/
theorem two_equal_of_iso {x y z : ℝ} (h : TgtAngles D x y z)
    (hiso : D.target.angleAt 0 = D.target.angleAt 2) : x = y ∨ x = z ∨ y = z := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  have hi : σ (σ.symm 0) = 0 := σ.apply_symm_apply 0
  have hj : σ (σ.symm 2) = 2 := σ.apply_symm_apply 2
  have hne : σ.symm 0 ≠ σ.symm 2 := fun h => absurd (σ.symm.injective h) (by decide)
  have : ∀ i j : Fin 3, i ≠ j → (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 0) ∨
      (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 2 ∧ j = 1) := by decide
  rcases this _ _ hne with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
    rw [a] at hi <;> rw [b] at hj
  · left; rw [← h0, ← h1, hi, hj, hiso]
  · right; left; rw [← h0, ← h2, hi, hj, hiso]
  · left; rw [← h0, ← h1, hi, hj, hiso]
  · right; right; rw [← h1, ← h2, hi, hj, hiso]
  · right; left; rw [← h0, ← h2, hi, hj, hiso]
  · right; right; rw [← h1, ← h2, hi, hj, hiso]

/-- In an isosceles triangle whose angles are `x, x, z`, the base angle is `x`. -/
theorem base_of_double {x z : ℝ} (h : TgtAngles D x x z)
    (hiso : D.target.angleAt 0 = D.target.angleAt 2) : D.target.angleAt 0 = x := by
  obtain ⟨σ, s0, s1, -⟩ := h
  have hσ : σ 0 ≠ σ 1 := fun h => absurd (σ.injective h) (by decide)
  have : ∀ i j : Fin 3, i ≠ j → (i = 0 ∨ i = 2) ∨ (j = 0 ∨ j = 2) := by decide
  rcases this (σ 0) (σ 1) hσ with (h | h) | (h | h)
  · rw [← s0, h]
  · rw [← s0, h, hiso]
  · rw [← s1, h]
  · rw [← s1, h, hiso]

/-- **Theorem `theorem:laczkovich-isosceles`** (Table `isosceles`). Let the isosceles,
non-equilateral triangle `ABC`, with base angles `θ` at `A` and `C`, be `N`-tiled by a tile.
Then (with `α ∉ ℚπ` in the last four lines):

1. `ABC` is similar to the tile;
2. the tile has angles `(θ, π/2 - θ, π/2)` (a right tile whose angle `θ` is the base angle);
3. the tile has angles `(θ, π - 3θ, 2θ)` (`γ = 2α`, base angles `α = θ`), `θ ∉ ℚπ`;
4. the tile has angles `(θ, π/3 - θ, 2π/3)` (`γ = 2π/3`, base angles `α = θ`), `θ ∉ ℚπ`;
5–7. the tile has angles `(α, β, 2α + β)` with `3α + 2β = π`, and `θ` is `α`, `β` or `α + β`.

In particular, if the angles of the tile are commensurable with `π`, one of the first two lines
holds. -/
theorem laczkovich_isosceles {θ : ℝ}
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = θ)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = θ)
    (hne : θ ≠ Real.pi / 3) :
    SimilarTM D ∨ TileAngles D θ (Real.pi / 2 - θ) (Real.pi / 2) ∨
    (IrrPi θ ∧ TileAngles D θ (Real.pi - 3 * θ) (2 * θ)) ∨
    (IrrPi θ ∧ TileAngles D θ (Real.pi / 3 - θ) (2 * Real.pi / 3)) ∨
    (∃ α β, IrrPi α ∧ 3 * α + 2 * β = Real.pi ∧ TileAngles D α β (2 * α + β) ∧
      (θ = α ∨ θ = β ∨ θ = α + β)) := by
  have ht0 : D.target.angleAt 0 = θ := hA
  have ht2 : D.target.angleAt 2 = θ := by rw [target_angleAt_2, hC]
  have hiso : D.target.angleAt 0 = D.target.angleAt 2 := ht0.trans ht2.symm
  have hpi := Real.pi_pos
  have noeq : Equilateral D → False := fun h => hne (ht0 ▸ h 0)
  -- The right-angle row: the base angle is the tile's `α`.
  have of_right : RightRow D → TileAngles D θ (Real.pi / 2 - θ) (Real.pi / 2) := by
    rintro ⟨α, β, hT, hG⟩
    have hαθ : θ = α := ht0 ▸ base_of_double D hG hiso
    obtain ⟨ρ, r0, r1, r2⟩ := hT
    have hs := D.model.angleAt_sum
    have hsum : α + β + Real.pi / 2 = Real.pi := by
      have := angleAt_sum3 D.model (p := ρ 0) (q := ρ 1) (r := ρ 2)
        (fun h => absurd (ρ.injective h) (by decide)) (fun h => absurd (ρ.injective h) (by decide))
        (fun h => absurd (ρ.injective h) (by decide))
      rw [r0, r1, r2] at this; exact this
    exact ⟨ρ, r0.trans hαθ.symm, by rw [r1, hαθ]; linarith, r2⟩
  by_cases hall : ∀ k, ∃ q : ℚ, D.model.angleAt k = q * Real.pi
  · rcases table_commensurable D hall with h | h | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl (of_right h))
    · exact (noeq h).elim
  push Not at hall
  obtain ⟨k, hk⟩ := hall
  have hirr : ∃ k, IrrPi (D.model.angleAt k) := ⟨k, fun ⟨q, hq⟩ => hk q hq⟩
  rcases table_incommensurable D hirr with h | h | ⟨h, -⟩ | ⟨α, hα, hT, hG⟩ |
      ⟨α, β, hα, hrel, hT, hG⟩ | ⟨α, hα, hT, hG⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl (of_right h))
  · exact (noeq h).elim
  · -- `γ = 2α`: the base angle is `α`.
    have hθ : θ = α := ht0 ▸ base_of_double D hG hiso
    subst hθ
    exact Or.inr (Or.inr (Or.inl ⟨hα, hT⟩))
  · -- `3α + 2β = π`: only the three isosceles shapes.
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨α, β, hα, hrel, hT, ?_⟩)))
    rcases hG with h | h | h | h | h
    · exact Or.inr (Or.inl (ht0 ▸ base_of_double D h hiso))
    · exact Or.inr (Or.inr (ht0 ▸ base_of_double D h hiso))
    · exfalso
      rcases two_equal_of_iso D h hiso with e | e | e
      · exact hα ⟨1 / 7, by push_cast; linarith⟩
      · exact hα ⟨1 / 5, by push_cast; linarith⟩
      · exact hα ⟨0, by push_cast; linarith⟩
    · exfalso
      rcases two_equal_of_iso D h hiso with e | e | e
      · exact hα ⟨0, by push_cast; linarith⟩
      · exact hα ⟨1 / 5, by push_cast; linarith⟩
      · exact hα ⟨1 / 4, by push_cast; linarith⟩
    · exact Or.inl (ht0 ▸ base_of_double D h hiso)
  · -- `γ = 2π/3`: only the isosceles shapes `(α, α, α + 3β)` and `(β, β, β + 3α)`.
    rcases hG with h | h | h | h
    · exact (noeq h).elim
    · rcases h with h | h
      · have hθ : θ = α := ht0 ▸ base_of_double D h hiso
        subst hθ
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hα, hT⟩)))
      · have hθ : θ = Real.pi / 3 - α := ht0 ▸ base_of_double D h hiso
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨fun ⟨q, hq⟩ => hα ⟨1 / 3 - q, ?_⟩, ?_⟩)))
        · push_cast; linarith
        · exact tileAngles_of_eq D hT.swap hθ.symm (by linarith) rfl
    · exfalso
      rcases h with h | h <;> rcases two_equal_of_iso D h hiso with e | e | e
      · exact hα ⟨1 / 3, by push_cast; linarith⟩
      · exact hα ⟨1 / 3, by push_cast; linarith⟩
      · exact hα ⟨1 / 3, by push_cast; linarith⟩
      · exact hα ⟨0, by push_cast; linarith⟩
      · exact hα ⟨0, by push_cast; linarith⟩
      · exact hα ⟨0, by push_cast; linarith⟩
    · exfalso
      rcases h with h | h | h | h | h <;> rcases two_equal_of_iso D h hiso with e | e | e
      · exact hα ⟨1 / 6, by push_cast; linarith⟩
      · exact hα ⟨1 / 6, by push_cast; linarith⟩
      · exact hα ⟨1 / 6, by push_cast; linarith⟩
      · exact hα ⟨0, by push_cast; linarith⟩
      · exact hα ⟨1 / 4, by push_cast; linarith⟩
      · exact hα ⟨1 / 5, by push_cast; linarith⟩
      · exact hα ⟨1 / 3, by push_cast; linarith⟩
      · exact hα ⟨1 / 12, by push_cast; linarith⟩
      · exact hα ⟨2 / 15, by push_cast; linarith⟩
      · exact hα ⟨2 / 9, by push_cast; linarith⟩
      · exact hα ⟨0, by push_cast; linarith⟩
      · exact hα ⟨1 / 9, by push_cast; linarith⟩
      · exact hα ⟨1 / 9, by push_cast; linarith⟩
      · exact hα ⟨0, by push_cast; linarith⟩
      · exact hα ⟨2 / 9, by push_cast; linarith⟩

end TriangleTiling.Laczkovich
