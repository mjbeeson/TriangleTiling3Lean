/-
`theorem:rationaltile120` (Section 11 of M. Beeson, *Tilings of an isosceles triangle*): if the
isosceles triangle `ABC` with base angles `α` (`α ∉ ℚπ`) is tiled by `(α, β, 2π/3)`, the tile is
rational.
-/
import TriangleTiling.Gamma120.ABRelation

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

/-- **The algebra of `theorem:rationaltile120`.** Relations `j c = p a + q b`, `J a = P b + Q c`
and `K b = L a + M c` (with `j, J, K > 0`) make `b / a` and `c / a` rational. -/
theorem rational_of_three_relations {a b c : ℝ} (ha : 0 < a)
    (h1 : ∃ j p q : ℕ, 0 < j ∧ (j : ℝ) * c = p * a + q * b)
    (h2 : ∃ J P Q : ℕ, 0 < J ∧ (J : ℝ) * a = P * b + Q * c)
    (h3 : ∃ K L M : ℕ, 0 < K ∧ (K : ℝ) * b = L * a + M * c) :
    ∃ r s : ℚ, b = r * a ∧ c = s * a := by
  obtain ⟨j, p, q, hj, e1⟩ := h1
  obtain ⟨J, P, Q, hJ, e2⟩ := h2
  obtain ⟨K, L, M, hK, e3⟩ := h3
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  by_cases hq : q = 0
  · -- `j c = p a`: `c / a = p / j`, and then `b / a` from the third relation.
    subst hq
    simp only [Nat.cast_zero, zero_mul, add_zero] at e1
    have hcs : c = ((p : ℚ) / j : ℚ) * a := by push_cast; field_simp; linarith
    refine ⟨((L : ℚ) + M * ((p : ℚ) / j)) / K, (p : ℚ) / j, ?_, hcs⟩
    push_cast
    field_simp
    rw [hcs] at e3
    push_cast at e3
    field_simp at e3
    linarith
  · -- Eliminate `c`: `(J j + P q ... )`. From `j c = p a + q b` and `J a = P b + Q c`:
    -- `j J a = j P b + Q (p a + q b)`, so `(j J - Q p) a = (j P + Q q) b` with `j P + Q q > 0`.
    have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
    have key : ((j : ℝ) * J - Q * p) * a = ((j : ℝ) * P + Q * q) * b := by
      have : (j : ℝ) * (J * a) = j * P * b + Q * (j * c) := by rw [e2]; ring
      rw [e1] at this
      linear_combination this
    have hden : (0 : ℝ) < (j : ℝ) * P + Q * q := by
      have : (0 : ℝ) ≤ (j : ℝ) * P := by positivity
      have : (0 : ℝ) ≤ (Q : ℝ) * q := by positivity
      rcases Nat.eq_zero_or_pos Q with hQ | hQ
      · -- `Q = 0`: then `J a = P b`, so `P > 0`.
        subst hQ
        simp only [Nat.cast_zero, zero_mul, add_zero] at e2 this ⊢
        rcases Nat.eq_zero_or_pos P with hP | hP
        · subst hP; simp at e2; rcases e2 with h | h <;> linarith
        · have : (0 : ℝ) < P := by exact_mod_cast hP
          positivity
      · have : (0 : ℝ) < Q := by exact_mod_cast hQ
        nlinarith
    have hbs : b = ((((j : ℚ) * J - Q * p) / (j * P + Q * q)) : ℚ) * a := by
      push_cast
      field_simp
      linarith
    refine ⟨((j : ℚ) * J - Q * p) / (j * P + Q * q),
      ((p : ℚ) + q * (((j : ℚ) * J - Q * p) / (j * P + Q * q))) / j, hbs, ?_⟩
    have hc2 : c = (p * a + q * b) / j := by field_simp; linarith
    rw [hc2, hbs]
    push_cast
    field_simp

variable {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * Real.pi / 3)
  (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
  (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
  (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D)
include hγ hirr hA hC

/-- **Theorem `theorem:rationaltile120`.** Let the isosceles triangle `ABC` with base angles `α`
(`α` not a rational multiple of `π`) be `N`-tiled by a tile with angles `(α, β, 2π/3)`. Then the
tile is rational: `b = r a` and `c = s a` with `r, s` rational. -/
theorem rationaltile120 : ∃ r s : ℚ,
    dist (D.model.pts 2) (D.model.pts 0) = r * dist (D.model.pts 1) (D.model.pts 2) ∧
    dist (D.model.pts 0) (D.model.pts 1) = s * dist (D.model.pts 1) (D.model.pts 2) := by
  obtain ⟨ha, -, -⟩ := model_sides_pos D
  obtain ⟨hra, hrb⟩ := abrelation D hγ hirr hA hC
  exact rational_of_three_relations ha (crelation D hγ hirr hA hC) hra hrb

end TriangleTiling
