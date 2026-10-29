/-
`theorem:possibletiles120` (Section 11 of M. Beeson, *Tilings of an isosceles triangle*).

If the isosceles triangle `ABC` with base angles `α` (`α ∉ ℚπ`) is `N`-tiled by `(α, β, 2π/3)`,
then, after scaling, the tile has integer sides `(a, b, c)` without a common factor
(`theorem:rationaltile120`), `c² = a² + b² + ab`, `2b + a` divides `N`, `N b = (2b + a) m²`, and
`ABC` has side `X = m c` and base `Y = m (2b + a)` (`lemma:2b+adividesN`). In particular
`a + 2b ≤ N`, so only finitely many tiles and triangles are possible for a given `N`.
-/
import TriangleTiling.Gamma120.RationalTile120
import TriangleTiling.Isosceles.Scaling
import TriangleTiling.Isosceles.GammaTwoPiThirdsArea

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

variable {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * Real.pi / 3)
  (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
  (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
  (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D)
include hγ hirr hA hC

/-- **Theorem `theorem:possibletiles120`** (with `lemma:2b+adividesN`). -/
theorem possibletiles120 : ∃ (κ : ℝ) (hκ : κ ≠ 0) (a b c m : ℕ),
    dist ((CongruentDissection.scale D κ hκ).model.pts 1)
      ((CongruentDissection.scale D κ hκ).model.pts 2) = a ∧
    dist ((CongruentDissection.scale D κ hκ).model.pts 2)
      ((CongruentDissection.scale D κ hκ).model.pts 0) = b ∧
    dist ((CongruentDissection.scale D κ hκ).model.pts 0)
      ((CongruentDissection.scale D κ hκ).model.pts 1) = c ∧
    Nat.gcd (Nat.gcd a b) c = 1 ∧ 0 < a ∧ 0 < b ∧ 0 < m ∧ c ^ 2 = a ^ 2 + b ^ 2 + a * b ∧
    (2 * b + a) ∣ N ∧ N * b = (2 * b + a) * m ^ 2 ∧
    dist ((CongruentDissection.scale D κ hκ).target.pts 0)
      ((CongruentDissection.scale D κ hκ).target.pts 1) = m * c ∧
    dist ((CongruentDissection.scale D κ hκ).target.pts 0)
      ((CongruentDissection.scale D κ hκ).target.pts 2) = m * (2 * b + a) := by
  obtain ⟨r, s, hb, hc⟩ := rationaltile120 D hγ hirr hA hC
  obtain ⟨κ, hκ, a, b, c, ha', hb', hc', hcop⟩ := int_scale_of_rational D r s hb hc
  set D' := CongruentDissection.scale D κ hκ
  have hγ' : ∠ (D'.model.pts 0) (D'.model.pts 2) (D'.model.pts 1) = 2 * Real.pi / 3 :=
    (tileγ_scale D hκ).trans hγ
  have hA' : ∠ (D'.target.pts 1) (D'.target.pts 0) (D'.target.pts 2) =
      ∠ (D'.model.pts 1) (D'.model.pts 0) (D'.model.pts 2) :=
    (angle_smul_smul' hκ _ _ _).trans (hA.trans (tileα_scale D hκ).symm)
  have hC' : ∠ (D'.target.pts 1) (D'.target.pts 2) (D'.target.pts 0) =
      ∠ (D'.model.pts 1) (D'.model.pts 0) (D'.model.pts 2) :=
    (angle_smul_smul' hκ _ _ _).trans (hC.trans (tileα_scale D hκ).symm)
  obtain ⟨hdvd, m, hNb, hX, hY⟩ := two_b_add_a_dvd_N D' ha' hb' hc' hcop hγ' hA' hC'
  obtain ⟨pa, pb, pc⟩ := model_sides_pos D'
  rw [ha'] at pa; rw [hb'] at pb; rw [hc'] at pc
  have hX0 := dist_pos.mpr (D'.target.indep.injective.ne (show (0 : Fin 3) ≠ 1 by decide))
  rw [hX] at hX0
  have hm : 0 < m := by
    have : (0 : ℝ) < m := pos_of_mul_pos_left hX0 (by positivity)
    exact_mod_cast this
  have hcab : c ^ 2 = a ^ 2 + b ^ 2 + a * b := by
    have := sq_eq_of_angle_two_pi_div_three ha' hb' hc' hγ'
    exact_mod_cast this
  exact ⟨κ, hκ, a, b, c, m, ha', hb', hc', hcop, by exact_mod_cast pa, by exact_mod_cast pb, hm,
    hcab, hdvd, hNb, hX, hY⟩

end TriangleTiling
