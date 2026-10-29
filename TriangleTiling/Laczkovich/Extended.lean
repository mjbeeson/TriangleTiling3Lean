/-
`theorem:laczkovich-extended` (Section 7 of M. Beeson, *Tilings of an isosceles triangle*):
Table `laczkovich-extended`, the possible `N` for an `N`-tiling of an isosceles (or equilateral)
triangle `ABC` by a tile whose angles are rational multiples of `π`.

| `ABC`                  | tile                     | `N`              | Lean            |
|------------------------|--------------------------|------------------|-----------------|
| similar to the tile    | `(α, β, γ)`              | `n²`             | `ExtRow` 1      |
| `(β, β, 2α)`           | `(α, β, π/2)`            | `2n²`            | `ExtRow` 2      |
| `(π/6, π/6, 2π/3)`     | `(π/6, π/3, π/2)`        | `6n²`            | `ExtRow` 3      |
| equilateral            | `(π/6, π/3, π/2)`        | `2n²` or `6n²`   | `ExtRow` 4      |
| equilateral            | `(π/6, π/6, 2π/3)`       | `3n²`            | `ExtRow` 5      |

The proof follows the paper: Table `laczkovich` (`table_commensurable`) gives the pairs of `ABC`
and tile, and the citations of the table give `N`:

* row 1 (Snover et al.): Bonfioli's `reptile_SWW` (Snover–Waiveris–Williams 1991, Beeson–Rosu
  Thm 5; NOTE/UNAUDITED in his library): `N` is a square, or the tile is right-angled;
* rows 2–4: `theorem:rationalisosceles` (with `lemma:baseangles` for the base angles);
* row 5: `lemma:equilateral120`.

A right-angled tile is handled by rows 2–4 whichever row of Table `laczkovich` it comes from; in
particular an isosceles right triangle tiled by itself with `N = m²` is put in row 1.
-/
import TriangleTiling.Laczkovich.BaseAngles
import TriangleTiling.Equilateral.Equilateral120
import Erdos634.Draft.LaczFormalT6

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
open TriangleTiling.Laczkovich

variable {N : ℕ} (D : CongruentDissection N)

/-- The rows of Table `laczkovich-extended`, for `ABC` with base angles at `A` and `C`
(`D.target.pts 0` and `D.target.pts 2`). -/
def ExtRow : Prop :=
  -- `ABC` similar to the tile, `N = n²`
  ((∃ x y z : ℝ, TileAngles D x y z ∧ TgtAngles D x y z) ∧ ∃ n : ℕ, N = n ^ 2) ∨
  -- `ABC = (β, β, 2α)`, tile `(α, β, π/2)`, `N = 2n²`
  ((∃ α : ℝ, TileAngles D α (∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2))
      (Real.pi / 2)) ∧ ∃ n : ℕ, N = 2 * n ^ 2) ∨
  -- `ABC = (π/6, π/6, 2π/3)`, tile `(π/6, π/3, π/2)`, `N = 6n²`
  (∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = Real.pi / 6 ∧
      TileAngles D (Real.pi / 6) (Real.pi / 3) (Real.pi / 2) ∧ ∃ n : ℕ, N = 6 * n ^ 2) ∨
  -- `ABC` equilateral, tile `(π/6, π/3, π/2)`, `N = 2n²` or `6n²`
  (Equilateral D ∧ TileAngles D (Real.pi / 6) (Real.pi / 3) (Real.pi / 2) ∧
      ((∃ n : ℕ, N = 2 * n ^ 2) ∨ ∃ n : ℕ, N = 6 * n ^ 2)) ∨
  -- `ABC` equilateral, tile `(π/6, π/6, 2π/3)`, `N = 3n²`
  (Equilateral D ∧ TileAngles D (Real.pi / 6) (Real.pi / 6) (2 * Real.pi / 3) ∧
      ∃ n : ℕ, N = 3 * n ^ 2)

/-! ### Relabelling the tile -/

theorem relabel_angleAt (τ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (relabelModel D τ).model.angleAt k = D.model.angleAt (τ k) :=
  (Row2.angleAt_comp D.model (relabelModel D τ).model τ (fun _ => rfl) k).1

theorem tileAngles_of_relabel (τ : Equiv.Perm (Fin 3)) {x y z : ℝ}
    (h : TileAngles (relabelModel D τ) x y z) : TileAngles D x y z := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  refine ⟨σ.trans τ, ?_, ?_, ?_⟩ <;> rw [Equiv.trans_apply, ← relabel_angleAt]
  · exact h0
  · exact h1
  · exact h2

theorem extRow_of_relabel (τ : Equiv.Perm (Fin 3)) (h : ExtRow (relabelModel D τ)) :
    ExtRow D := by
  rcases h with ⟨⟨x, y, z, hT, hA⟩, hN⟩ | ⟨⟨α, hT⟩, hN⟩ | ⟨hA, hT, hN⟩ | ⟨hE, hT, hN⟩ |
      ⟨hE, hT, hN⟩
  · exact Or.inl ⟨⟨x, y, z, tileAngles_of_relabel D τ hT, hA⟩, hN⟩
  · exact Or.inr (Or.inl ⟨⟨α, tileAngles_of_relabel D τ hT⟩, hN⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hA, tileAngles_of_relabel D τ hT, hN⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hE, tileAngles_of_relabel D τ hT, hN⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hE, tileAngles_of_relabel D τ hT, hN⟩)))

/-! ### A right-angled tile -/

/-- The tile's angles `tileα, tileβ, tileγ` as an unordered triple. -/
theorem tileAngles_id : TileAngles D (tileα D) (tileβ D) (tileγ D) :=
  ⟨1, rfl, rfl, rfl⟩

/-- An isosceles `ABC` with base angles `θ`: its angles are `θ, θ, π - 2θ`. -/
theorem tgt_iso {θ : ℝ} (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = θ)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = θ) :
    TgtAngles D θ θ (Real.pi - 2 * θ) :=
  tgt_of_two D (i := 0) (j := 2) (by decide) hA (by rw [target_angleAt_2]; exact hC)

/-- An isosceles `ABC` with base angles `π/3` is equilateral. -/
theorem equilateral_of_base (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) =
      Real.pi / 3)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = Real.pi / 3) :
    Equilateral D := by
  have h0 : D.target.angleAt 0 = Real.pi / 3 := hA
  have h2 : D.target.angleAt 2 = Real.pi / 3 := by rw [target_angleAt_2]; exact hC
  have hs := D.target.angleAt_sum
  intro k
  have : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  rcases this k with rfl | rfl | rfl
  · exact h0
  · linarith
  · exact h2

/-- Rows 2–4 (and row 1 for the isosceles right triangle), when the tile has its right angle at
vertex 2 and the base angles of `ABC` are `tileβ`: `theorem:rationalisosceles`. -/
theorem extRow_right_beta (hright : tileγ D = Real.pi / 2)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D)
    (hrat : ∃ r : ℚ, tileα D = r * Real.pi) : ExtRow D := by
  have hsum : tileα D + tileβ D + tileγ D = Real.pi := D.model.angleAt_sum
  have hT := tileAngles_id D
  rw [hright] at hT
  rcases rationalisosceles D hright hA hC hrat with hN | ⟨hN, hβ⟩ | ⟨hN, ⟨hβ, hα⟩ | ⟨hβ, hα⟩⟩
  · exact Or.inr (Or.inl ⟨⟨tileα D, by rw [hA]; exact hT⟩, hN⟩)
  · -- `ABC` and the tile are both `(π/4, π/4, π/2)`
    have hα : tileα D = Real.pi / 4 := by linarith
    rw [hα, hβ] at hT
    refine Or.inl ⟨⟨Real.pi / 4, Real.pi / 4, Real.pi / 2, hT, ?_⟩, hN⟩
    have h := tgt_iso D (hA.trans hβ) (hC.trans hβ)
    rwa [show Real.pi - 2 * (Real.pi / 4) = Real.pi / 2 by ring] at h
  · refine Or.inr (Or.inr (Or.inl ⟨hA.trans hβ, ⟨Equiv.swap 0 1, ?_, ?_, ?_⟩, hN⟩))
    · rw [Equiv.swap_apply_left]; exact hβ
    · rw [Equiv.swap_apply_right]; exact hα
    · rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; exact hright
  · rw [hα, hβ] at hT
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨equilateral_of_base D (hA.trans hβ) (hC.trans hβ),
      hT, Or.inr hN⟩)))

/-- A right-angled tile with its right angle at vertex 2: rows 1–4, by `lemma:baseangles` and
`theorem:rationalisosceles`. -/
theorem extRow_right (hright : tileγ D = Real.pi / 2)
    (hiso : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) =
      ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0))
    (hrat : ∀ k, ∃ q : ℚ, D.model.angleAt k = q * Real.pi) : ExtRow D := by
  rcases baseangles D hright hiso with ⟨hA, hC⟩ | ⟨hA, hC⟩
  · exact extRow_right_beta D hright hA hC (hrat 0)
  · obtain ⟨eα, eβ, eγ⟩ := swap_angles D
    refine extRow_of_relabel D (Equiv.swap 0 1) (extRow_right_beta _ (eγ.trans hright)
      (hA.trans eβ.symm) (hC.trans eβ.symm) ?_)
    rw [eα]; exact hrat 1

/-! ### The theorem -/

/-- A triple of tile angles containing `π/2` gives a right angle at some vertex. -/
theorem right_of_tileAngles {x y z : ℝ} (h : TileAngles D x y z)
    (hr : x = Real.pi / 2 ∨ y = Real.pi / 2 ∨ z = Real.pi / 2) :
    ∃ k, D.model.angleAt k = Real.pi / 2 := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  rcases hr with rfl | rfl | rfl
  · exact ⟨σ 0, h0⟩
  · exact ⟨σ 1, h1⟩
  · exact ⟨σ 2, h2⟩

/-- **Theorem `theorem:laczkovich-extended`.** Let the isosceles or equilateral triangle `ABC`
(angles at `A` and `C` equal) be `N`-tiled by a tile whose angles are rational multiples of `π`.
Then `ABC`, the tile and `N` are as in one of the rows of Table `laczkovich-extended`
(`ExtRow`). -/
theorem laczkovich_extended
    (hrat : ∀ k, ∃ q : ℚ, D.model.angleAt k = q * Real.pi)
    (hiso : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) =
      ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0)) :
    ExtRow D := by
  by_cases hR : ∃ k, D.model.angleAt k = Real.pi / 2
  · -- move the right angle to vertex 2
    obtain ⟨k, hk⟩ := hR
    refine extRow_of_relabel D (Equiv.swap k 2) (extRow_right _ ?_ hiso ?_)
    · change (relabelModel D (Equiv.swap k 2)).model.angleAt 2 = _
      rw [relabel_angleAt, Equiv.swap_apply_right]; exact hk
    · intro j; rw [relabel_angleAt]; exact hrat _
  rcases table_commensurable D hrat with hs | ⟨α, β, hT, -⟩ | ⟨hT, hE⟩
  · rcases Erdos634.Draft.LaczFormal.reptile_SWW D hs with ⟨n, hn⟩ |
        ⟨A, B, -, i, j, k, -, -, -, hk, -⟩ | ⟨-, hT⟩
    · obtain ⟨μ, τ, h⟩ := hs
      refine Or.inl ⟨⟨D.target.angleAt 0, D.target.angleAt 1, D.target.angleAt 2,
        ⟨τ, (h 0).1.symm, (h 1).1.symm, (h 2).1.symm⟩, ⟨1, rfl, rfl, rfl⟩⟩, n, ?_⟩
      rw [hn]; ring
    · exact absurd ⟨k, hk⟩ hR
    · exact absurd (right_of_tileAngles D hT (Or.inr (Or.inr rfl))) hR
  · exact absurd (right_of_tileAngles D hT (Or.inr (Or.inr rfl))) hR
  · -- row 5: `lemma:equilateral120`
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hE, hT, ?_⟩)))
    obtain ⟨σ, h0, h1, -⟩ := hT
    exact equilateral120 (relabelModel D σ) ((relabel_angleAt D σ 0).trans h0)
      ((relabel_angleAt D σ 1).trans h1) (hE 0) (hE 1)

end TriangleTiling

#print axioms TriangleTiling.laczkovich_extended
