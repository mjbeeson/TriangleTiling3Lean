/-
The remark after `theorem:rationaltile`: a rational tile can be scaled to have integer sides
without a common factor. With it, the results first proved for such tiles
(`notsquarefree_int`, `N45_int`, `N_div_4_helper_int`) hold as the paper states them, for any tile
`(α, β, 2α)` with `α ∉ ℚπ` tiling the isosceles triangle with base angles `α`.
-/
import TriangleTiling.Tiling.Scale
import TriangleTiling.Isosceles.RationalTile

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

variable {N : ℕ} (D : CongruentDissection N) {κ : ℝ} (hκ : κ ≠ 0)

theorem tileα_scale : tileα (CongruentDissection.scale D κ hκ) = tileα D :=
  angle_smul_smul' hκ _ _ _

theorem tileβ_scale : tileβ (CongruentDissection.scale D κ hκ) = tileβ D :=
  angle_smul_smul' hκ _ _ _

theorem tileγ_scale : tileγ (CongruentDissection.scale D κ hκ) = tileγ D :=
  angle_smul_smul' hκ _ _ _

/-- The hypotheses of the isosceles results carry over to the scaled tiling. -/
theorem scale_hyps (hγ : tileγ D = 2 * tileα D) (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D) :
    let D' := CongruentDissection.scale D κ hκ
    tileγ D' = 2 * tileα D' ∧ (¬ ∃ r : ℚ, tileα D' = (r : ℝ) * Real.pi) ∧
      ∠ (D'.target.pts 1) (D'.target.pts 0) (D'.target.pts 2) = tileα D' ∧
      ∠ (D'.target.pts 1) (D'.target.pts 2) (D'.target.pts 0) = tileα D' := by
  intro D'
  refine ⟨by rw [tileγ_scale, tileα_scale]; exact hγ, by rw [tileα_scale]; exact hirr, ?_, ?_⟩
  · exact (angle_smul_smul' hκ _ _ _).trans (hA.trans (tileα_scale D hκ).symm)
  · exact (angle_smul_smul' hκ _ _ _).trans (hC.trans (tileα_scale D hκ).symm)

/-- **Integer sides, for any rational tile.** If `b = r a` and `c = s a` with `r, s` rational, some
scaling of the tiling has a tile with integer sides `a, b, c` without a common factor. -/
theorem int_scale_of_rational (r s : ℚ)
    (hb : dist (D.model.pts 2) (D.model.pts 0) = r * dist (D.model.pts 1) (D.model.pts 2))
    (hc : dist (D.model.pts 0) (D.model.pts 1) = s * dist (D.model.pts 1) (D.model.pts 2)) : ∃ (κ : ℝ) (hκ : κ ≠ 0) (a b c : ℕ),
    dist ((CongruentDissection.scale D κ hκ).model.pts 1)
      ((CongruentDissection.scale D κ hκ).model.pts 2) = a ∧
    dist ((CongruentDissection.scale D κ hκ).model.pts 2)
      ((CongruentDissection.scale D κ hκ).model.pts 0) = b ∧
    dist ((CongruentDissection.scale D κ hκ).model.pts 0)
      ((CongruentDissection.scale D κ hκ).model.pts 1) = c ∧
    Nat.gcd (Nat.gcd a b) c = 1 := by
  obtain ⟨ha0, hb0, hc0⟩ := model_sides_pos D
  set a0 := dist (D.model.pts 1) (D.model.pts 2)
  set b0 := dist (D.model.pts 2) (D.model.pts 0)
  set c0 := dist (D.model.pts 0) (D.model.pts 1)
  have hr : (0 : ℝ) < r := by
    rw [hb] at hb0; exact pos_of_mul_pos_left hb0 ha0.le
  have hs : (0 : ℝ) < s := by
    rw [hc] at hc0; exact pos_of_mul_pos_left hc0 ha0.le
  have hrn : 0 < r.num := Rat.num_pos.mpr (by exact_mod_cast hr)
  have hsn : 0 < s.num := Rat.num_pos.mpr (by exact_mod_cast hs)
  -- `a0 : b0 : c0 = A : B : C`.
  set A := r.den * s.den
  set B := r.num.toNat * s.den
  set C := s.num.toNat * r.den
  have hA0 : 0 < A := Nat.mul_pos r.den_pos s.den_pos
  have hrA : (r : ℝ) * A = B := by
    have : (r.num.toNat : ℝ) = r.num := by exact_mod_cast Int.toNat_of_nonneg hrn.le
    simp only [A, B, Nat.cast_mul, this]
    rw [Rat.cast_def]
    field_simp
  have hsA : (s : ℝ) * A = C := by
    have : (s.num.toNat : ℝ) = s.num := by exact_mod_cast Int.toNat_of_nonneg hsn.le
    simp only [A, C, Nat.cast_mul, this]
    rw [Rat.cast_def]
    field_simp
  -- Divide out the common factor.
  set g := Nat.gcd (Nat.gcd A B) C
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.gcd_pos_of_pos_left _ hA0)
  have hgA : g ∣ A := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have hgB : g ∣ B := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have hgC : g ∣ C := Nat.gcd_dvd_right _ _
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  set κ : ℝ := A / (g * a0)
  have hκpos : 0 < κ := by
    have : (0 : ℝ) < A := by exact_mod_cast hA0
    positivity
  refine ⟨κ, hκpos.ne', A / g, B / g, C / g, ?_, ?_, ?_, ?_⟩
  · rw [CongruentDissection.scale_model_pts, CongruentDissection.scale_model_pts, dist_smul_smul,
      abs_of_pos hκpos, Nat.cast_div hgA hgR.ne']
    change κ * a0 = _
    simp only [κ]
    field_simp
  · rw [CongruentDissection.scale_model_pts, CongruentDissection.scale_model_pts, dist_smul_smul,
      abs_of_pos hκpos, Nat.cast_div hgB hgR.ne', ← hrA]
    change κ * b0 = _
    rw [hb]
    simp only [κ]
    field_simp
  · rw [CongruentDissection.scale_model_pts, CongruentDissection.scale_model_pts, dist_smul_smul,
      abs_of_pos hκpos, Nat.cast_div hgC hgR.ne', ← hsA]
    change κ * c0 = _
    rw [hc]
    simp only [κ]
    field_simp
  · rw [Nat.gcd_div hgA hgB, Nat.gcd_div (Nat.gcd_dvd_left _ _) hgC, Nat.div_self hg]

variable (hγ : tileγ D = 2 * tileα D) (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
  (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
  (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D)
include hγ hirr hA hC

/-- **Integer sides.** Some scaling of the tiling has a tile with integer sides `a, b, c` without
a common factor. -/
theorem exists_int_scale : ∃ (κ : ℝ) (hκ : κ ≠ 0) (a b c : ℕ),
    dist ((CongruentDissection.scale D κ hκ).model.pts 1)
      ((CongruentDissection.scale D κ hκ).model.pts 2) = a ∧
    dist ((CongruentDissection.scale D κ hκ).model.pts 2)
      ((CongruentDissection.scale D κ hκ).model.pts 0) = b ∧
    dist ((CongruentDissection.scale D κ hκ).model.pts 0)
      ((CongruentDissection.scale D κ hκ).model.pts 1) = c ∧
    Nat.gcd (Nat.gcd a b) c = 1 := by
  obtain ⟨r, s, hb, hc⟩ := rationaltile D hγ hirr hA hC
  exact int_scale_of_rational D r s hb hc

/-- **Theorem `theorem:notsquarefree`.** If the isosceles triangle `ABC` with base angles `α`
(`α` not a rational multiple of `π`) is `N`-tiled by a tile with angles `(α, β, 2α)`, then `N` is
not squarefree. -/
theorem notsquarefree : ¬ Squarefree N := by
  obtain ⟨κ, hκ, a, b, c, ha, hb, hc, hcop⟩ := exists_int_scale D hγ hirr hA hC
  obtain ⟨hγ', hirr', hA', hC'⟩ := scale_hyps D hκ hγ hirr hA hC
  exact notsquarefree_int _ ha hb hc hcop hγ' hirr' hA' hC'

/-- **Theorem `theorem:N45`.** If the isosceles triangle `ABC` with base angles `α` (`α` not a
rational multiple of `π`) is `N`-tiled by a tile with angles `(α, β, 2α)`, then `N ≥ 45`. -/
theorem N45 : 45 ≤ N := by
  obtain ⟨κ, hκ, a, b, c, ha, hb, hc, hcop⟩ := exists_int_scale D hγ hirr hA hC
  obtain ⟨hγ', hirr', hA', hC'⟩ := scale_hyps D hκ hγ hirr hA hC
  exact N45_int _ ha hb hc hcop hγ' hirr' hA' hC'

/-- **Lemma `lemma:N/4helper`.** In such a tiling no tile has one vertex strictly inside `AB` and
another strictly inside `BC`. -/
theorem N_div_4_helper (j : Fin N) (k k' : Fin 3) (hkk : k ≠ k')
    (hE : (D.tile j).pts k ∈ openSegment ℝ (D.target.pts 0) (D.target.pts 1))
    (hF : (D.tile j).pts k' ∈ openSegment ℝ (D.target.pts 1) (D.target.pts 2)) : False := by
  obtain ⟨κ, hκ, a, b, c, ha, hb, hc, hcop⟩ := exists_int_scale D hγ hirr hA hC
  obtain ⟨hγ', hirr', hA', hC'⟩ := scale_hyps D hκ hγ hirr hA hC
  exact N_div_4_helper_int _ ha hb hc hcop hγ' hirr' hA' hC' j k k' hkk
    (smul_mem_openSegment κ hE) (smul_mem_openSegment κ hF)

end TriangleTiling
