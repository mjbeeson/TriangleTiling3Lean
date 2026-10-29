/-
Results of Sections 2–4 of M. Beeson, *Triangle tiling: the case 3α + 2β = π*
(arXiv 1206.2229v4) that rest on `lemma:angles`, i.e. on Laczkovich's Theorems 5.1 and 5.3.

Lean names follow the TeX labels. Vocabulary: `TriangleTiling.ThreeAlpha.Defs`.
-/
import TriangleTiling.Laczkovich.BaseAngles
import TriangleTiling.ThreeAlpha.Coloring
import Erdos634.Draft.LaczFormalClassifyAll

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles similar_of_same_angles)
open Erdos634.BeesonColoring TriangleTiling.Laczkovich

variable {N : ℕ} (D : CongruentDissection N)

/-! ### From the paper's hypotheses to Bonfioli's -/

theorem tgtAngles_of_triple3 {x y z : ℝ}
    (h : Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) x y z) :
    TgtAngles D x y z := by
  rcases h with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
      ⟨h0, h1, h2⟩
  · obtain ⟨τ, t0, t1, t2⟩ := perm3 0 1 2 (by decide) (by decide) (by decide)
    exact ⟨τ, by rw [t0, h0], by rw [t1, h1], by rw [t2, h2]⟩
  · obtain ⟨τ, t0, t1, t2⟩ := perm3 0 2 1 (by decide) (by decide) (by decide)
    exact ⟨τ, by rw [t0, h0], by rw [t1, h2], by rw [t2, h1]⟩
  · obtain ⟨τ, t0, t1, t2⟩ := perm3 1 0 2 (by decide) (by decide) (by decide)
    exact ⟨τ, by rw [t0, h1], by rw [t1, h0], by rw [t2, h2]⟩
  · obtain ⟨τ, t0, t1, t2⟩ := perm3 2 0 1 (by decide) (by decide) (by decide)
    exact ⟨τ, by rw [t0, h2], by rw [t1, h0], by rw [t2, h1]⟩
  · obtain ⟨τ, t0, t1, t2⟩ := perm3 1 2 0 (by decide) (by decide) (by decide)
    exact ⟨τ, by rw [t0, h1], by rw [t1, h2], by rw [t2, h0]⟩
  · obtain ⟨τ, t0, t1, t2⟩ := perm3 2 1 0 (by decide) (by decide) (by decide)
    exact ⟨τ, by rw [t0, h2], by rw [t1, h1], by rw [t2, h0]⟩

/-- The tile's angles: positive, summing to `π`, with `γ = 2α + β`. -/
theorem tile_facts {α β γ : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hT : TileAngles D α β γ) :
    0 < α ∧ 0 < β ∧ γ = 2 * α + β := by
  obtain ⟨σ, h0, h1, h2⟩ := hT
  have hs := D.model.angleAt_sum
  have hsum : D.model.angleAt (σ 0) + D.model.angleAt (σ 1) + D.model.angleAt (σ 2) = Real.pi := by
    have e := Equiv.sum_comp σ (fun k => D.model.angleAt k)
    simp only [Fin.sum_univ_three] at e
    rw [e, hs]
  refine ⟨h0 ▸ Tri.angleAt_pos' _ _, h1 ▸ Tri.angleAt_pos' _ _, ?_⟩
  rw [h0, h1, h2] at hsum
  linarith

theorem threeAlphaData_of {α β γ : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileAngles D α β γ) :
    ∃ a b c : ℝ, D.model.ThreeAlphaData α β a b c := by
  have hγ := (tile_facts D hrel hT).2.2
  obtain ⟨σ, h0, h1, h2⟩ := hT
  exact ⟨_, _, _, σ, h0, rfl, h1, rfl, hγ ▸ h2, rfl⟩

theorem threeAlphaData_of_sides {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) : D.model.ThreeAlphaData α β a b c := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  have hγ := (tile_facts D hrel ⟨σ, h0, h1, h2⟩).2.2
  exact ⟨σ, h0, l0, h1, l1, hγ ▸ h2, l2⟩

theorem not_triple3 {α β γ : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hT : TileAngles D α β γ)
    (hns : ¬ SimilarTM D) :
    ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β) := by
  have hγ := (tile_facts D hrel hT).2.2
  intro h3
  exact hns (similar_of_same_angles D hT (hγ ▸ tgtAngles_of_triple3 D h3))


/-- **Lemma `lemma:angles`.** Let `3α + 2β = π`, and suppose `ABC` is `N`-tiled by a tile with
angles `(α, β, γ)`, not similar to `ABC`. Then `α` and `β` are not rational multiples of `π`,
and every rational linear relation between `π`, `α` and `β` is a rational multiple of
`3α + 2β = π`. -/
theorem angles {α β γ : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hT : TileAngles D α β γ)
    (hns : ¬ SimilarTM D) :
    IrrPi α ∧ IrrPi β ∧
      ∀ x y z : ℚ, (y : ℝ) * α + z * β = x * Real.pi → ∃ t : ℚ, y = 3 * t ∧ z = 2 * t ∧ x = t := by
  obtain ⟨hα, hβ, hγ⟩ := tile_facts D hrel hT
  have hπ := Real.pi_pos
  have hirr : IrrPi α := by
    rintro ⟨r, hr⟩
    have hall : ∀ k, ∃ q : ℚ, D.model.angleAt k = q * Real.pi := by
      intro k
      rcases tileAngles_mem D hT k with e | e | e <;> rw [e]
      · exact ⟨r, hr⟩
      · exact ⟨(1 - 3 * r) / 2, by push_cast; linarith⟩
      · exact ⟨(1 + r) / 2, by push_cast; linarith⟩
    rcases table_commensurable D hall with hs | ⟨x, y, hR, -⟩ | ⟨hE, -⟩
    · exact hns hs
    · obtain ⟨τ, -, -, hτ⟩ := hR
      rcases tileAngles_mem D hT (τ 2) with e | e | e <;> rw [hτ] at e <;> linarith
    · obtain ⟨σ, h0, h1, -⟩ := hT
      have m0 := tileAngles_mem D hE (σ 0)
      have m1 := tileAngles_mem D hE (σ 1)
      rw [h0] at m0
      rw [h1] at m1
      rcases m0 with e | e | e <;> rcases m1 with f | f | f <;> linarith
  refine ⟨hirr, ?_, ?_⟩
  · rintro ⟨r, hr⟩
    exact hirr ⟨(1 - 2 * r) / 3, by push_cast; linarith⟩
  · intro x y z e
    have key : (((y : ℝ)) - 3 * z / 2) * α = ((x : ℝ) - z / 2) * Real.pi := by
      linear_combination e - (z : ℝ) / 2 * hrel
    by_cases hc : (y : ℝ) - 3 * z / 2 = 0
    · have hx : ((x : ℝ) - z / 2) * Real.pi = 0 := by rw [hc, zero_mul] at key; linarith
      have hx' : (x : ℝ) = z / 2 := by
        rcases mul_eq_zero.mp hx with e | e
        · linarith
        · exact absurd e Real.pi_ne_zero
      refine ⟨z / 2, ?_, by ring, ?_⟩
      · exact_mod_cast (show (y : ℝ) = 3 * ((z : ℝ) / 2) by linarith)
      · exact_mod_cast hx'
    · exfalso
      apply hirr
      refine ⟨(x - z / 2) / (y - 3 * z / 2), ?_⟩
      push_cast
      rw [div_mul_eq_mul_div, eq_div_iff hc]
      linear_combination key

/-- **Lemma `lemma:nogamma`.** Let `ABC` be `N`-tiled by a tile with angles `(α, β, γ)`, where
`3α + 2β = π`, and suppose `ABC` is not similar to the tile. Then no tile has its `γ` angle at a
vertex of `ABC`, and there are exactly five tiles with vertices at the vertices of `ABC`. -/
theorem nogamma {α β γ : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hT : TileAngles D α β γ)
    (hns : ¬ SimilarTM D) :
    (∀ (k : Fin 3) (i : Fin N) (l : Fin 3),
        (D.tile i).pts l = D.target.pts k → (D.tile i).angleAt l ≠ γ) ∧
      ∑ k, tilesAt D k = 5 := by
  have hγ := (tile_facts D hrel hT).2.2
  obtain ⟨a, b, c, h⟩ := threeAlphaData_of D hrel hT
  have hirr := (angles D hrel hT hns).1
  subst hγ
  exact nogamma_irr D hirr hrel h (not_triple3 D hrel hT hns)

/-- **Lemma `lemma:shapes`.** Suppose `3α + 2β = π` and `ABC` is `N`-tiled by a tile with
angles `(α, β, γ)`, not similar to `ABC`. Then the angles of `ABC` are one of the five triples
`(α, α + 2β, α)`, `(β, 3α, β)`, `(α + β, α, α + β)`, `(2α, β, α + β)`, `(2α, α, 2β)`,
and there are exactly three `α` angles and two `β` angles of tiles at the vertices of `ABC`. -/
theorem shapes {α β γ : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hT : TileAngles D α β γ)
    (hns : ¬ SimilarTM D) :
    (TgtAngles D α (α + 2 * β) α ∨ TgtAngles D β (3 * α) β ∨ TgtAngles D (α + β) α (α + β) ∨
        TgtAngles D (2 * α) β (α + β) ∨ TgtAngles D (2 * α) α (2 * β)) ∧
      ∑ k, anglesAt D k α = 3 ∧ ∑ k, anglesAt D k β = 2 := by
  obtain ⟨a, b, c, h⟩ := threeAlphaData_of D hrel hT
  have hirr := (angles D hrel hT hns).1
  obtain ⟨h5, h3, h2⟩ := shapes_irr D hirr hrel h (not_triple3 D hrel hT hns)
  refine ⟨?_, h3, h2⟩
  rcases h5 with e | e | e | e | e
  · exact Or.inl (tgtAngles_of_triple3 D e)
  · exact Or.inr (Or.inl (tgtAngles_of_triple3 D e))
  · exact Or.inr (Or.inr (Or.inl (tgtAngles_of_triple3 D e)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (tgtAngles_of_triple3 D e))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (tgtAngles_of_triple3 D e))))

-- The coloring exists with any given tile black; that `i₀` is at `B` is not needed.
set_option linter.unusedVariables false in
/-- **Lemma `lemma:signedtiles`.** Suppose `ABC` is `N`-tiled by a tile with angles
`(α, β, γ)`, `3α + 2β = π`, and `ABC` is not similar to the tile. Then the tiles can be colored
black (`1`) and white (`-1`) so that tiles on opposite sides of each interior edge get opposite
colors, with a specified tile at vertex `B` black. -/
theorem signedtiles {α β γ : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hT : TileAngles D α β γ)
    (hns : ¬ SimilarTM D) {i₀ : Fin N} (hi₀ : TileAt D 1 i₀) :
    ∃ ε : Fin N → ℤ, D.toDissection.ProperColouring ε ∧ ε i₀ = 1 := by
  obtain ⟨a, b, c, h⟩ := threeAlphaData_of D hrel hT
  exact signedtiles_irr D (angles D hrel hT hns).1 hrel h i₀

/-- **Theorem `theorem:coloring`** (coloring theorem). Let `3α + 2β = π`, and suppose `ABC` is
`N`-tiled by a tile with angles `(α, β, γ)`, not similar to `ABC`. The vertices can be labeled
so that `A` and `C` have the same number of tiles at them. With such a labeling, color the tiles
as in `lemma:signedtiles` with a tile at `B` having an edge on `AB` black, and let `M` be the
number of black tiles minus the number of white tiles. Then
`M (a + b + c) = X ± Y + Z`, where `(X, Y, Z)` are the lengths of `(BC, AC, AB)`, with the plus
sign if `ABC` is isosceles with base angles `α` or `β` (at `A` and `C`), and the minus sign in
the three remaining cases. -/
theorem coloring {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D) :
    (∃ σ : Equiv.Perm (Fin 3), tilesAt D (σ 0) = tilesAt D (σ 2)) ∧
      (tilesAt D 0 = tilesAt D 2 → ∀ (ε : Fin N → ℤ) (i₀ : Fin N),
        D.toDissection.ProperColouring ε → AtBOnAB D i₀ → ε i₀ = 1 →
        let M : ℤ := ∑ i, ε i
        let X := D.target.oppLen 0
        let Y := D.target.oppLen 1
        let Z := D.target.oppLen 2
        ((D.target.angleAt 0 = α ∧ D.target.angleAt 2 = α) ∨
            (D.target.angleAt 0 = β ∧ D.target.angleAt 2 = β) →
          (M : ℝ) * (a + b + c) = X + Y + Z) ∧
        (¬ ((D.target.angleAt 0 = α ∧ D.target.angleAt 2 = α) ∨
            (D.target.angleAt 0 = β ∧ D.target.angleAt 2 = β)) →
          (M : ℝ) * (a + b + c) = X - Y + Z)) := by
  have hT' : TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    exact ⟨σ, h0, h1, h2⟩
  exact coloring_irr D (angles D hrel hT' hns).1 hrel (threeAlphaData_of_sides D hrel hT)
    (not_triple3 D hrel hT' hns)

/-- **Lemma `lemma:Mnotzero`.** Let `3α + 2β = π`, and suppose `ABC` is `N`-tiled by a tile with
angles `(α, β, γ)`, not similar to `ABC`. Color the tiles as in `lemma:signedtiles`, and let `M`
be the number of black tiles minus the number of white tiles. Then `M ≠ 0`. -/
theorem Mnotzero {α β γ : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hT : TileAngles D α β γ)
    (hns : ¬ SimilarTM D) {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) :
    ∑ i, ε i ≠ 0 := by
  obtain ⟨a, b, c, h⟩ := threeAlphaData_of D hrel hT
  exact Mnotzero_irr D (angles D hrel hT hns).1 hrel h (not_triple3 D hrel hT hns) hε

end TriangleTiling.ThreeAlpha
