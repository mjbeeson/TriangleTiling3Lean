/-
The field `ℚ(l)` for an irrational `l` with `l²` rational (in the paper, `l = λ = √(N/2)`).

Its elements are the reals `x l + y` with `x, y` rational. They are closed under the field
operations, `x l + y = 0` only when `x = y = 0`, and each is a root of a nonzero rational
polynomial of degree at most `2` (which is how `lemma:euler` applies to them).
-/
import TriangleTiling.Isosceles.Euler

namespace TriangleTiling

open Polynomial

/-- `v` lies in `ℚ(l)`: `v = x l + y` with `x, y` rational. -/
def InQ (l v : ℝ) : Prop := ∃ x y : ℚ, v = x * l + y

section

variable {l : ℝ} {d : ℚ} (hl : l ^ 2 = d) (hirr : ¬ ∃ q : ℚ, l = q)

theorem InQ.rat (q : ℚ) : InQ l q := ⟨0, q, by simp⟩

theorem InQ.self : InQ l l := ⟨1, 0, by simp⟩

theorem InQ.add {v w : ℝ} (hv : InQ l v) (hw : InQ l w) : InQ l (v + w) := by
  obtain ⟨x, y, rfl⟩ := hv
  obtain ⟨z, u, rfl⟩ := hw
  exact ⟨x + z, y + u, by push_cast; ring⟩

theorem InQ.neg {v : ℝ} (hv : InQ l v) : InQ l (-v) := by
  obtain ⟨x, y, rfl⟩ := hv
  exact ⟨-x, -y, by push_cast; ring⟩

theorem InQ.sub {v w : ℝ} (hv : InQ l v) (hw : InQ l w) : InQ l (v - w) := by
  rw [sub_eq_add_neg]; exact hv.add hw.neg

include hl in
theorem InQ.mul {v w : ℝ} (hv : InQ l v) (hw : InQ l w) : InQ l (v * w) := by
  obtain ⟨x, y, rfl⟩ := hv
  obtain ⟨z, u, rfl⟩ := hw
  refine ⟨x * u + y * z, x * z * d + y * u, ?_⟩
  push_cast
  linear_combination (↑x * ↑z) * hl

include hirr in
/-- `x l + y = 0` only for `x = y = 0`. -/
theorem InQ.indep {x y : ℚ} (h : (x : ℝ) * l + y = 0) : x = 0 ∧ y = 0 := by
  by_cases hx : x = 0
  · subst hx
    simp at h
    exact ⟨rfl, by exact_mod_cast h⟩
  · exfalso
    apply hirr
    refine ⟨-y / x, ?_⟩
    have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast hx
    push_cast
    field_simp
    linarith

include hl hirr in
theorem InQ.inv {v : ℝ} (hv : InQ l v) (hv0 : v ≠ 0) : InQ l v⁻¹ := by
  obtain ⟨x, y, rfl⟩ := hv
  -- `(x l + y)(y - x l) = y² - x² d`, a nonzero rational.
  have hden : (y : ℝ) ^ 2 - (x : ℝ) ^ 2 * d ≠ 0 := by
    intro h
    have h1 : ((x : ℝ) * l + y) * (y - x * l) = 0 := by
      linear_combination h - (↑x ^ 2) * hl
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hv0 h2
    · obtain ⟨hx, hy⟩ := InQ.indep hirr (x := -x) (y := y) (by push_cast; linarith)
      apply hv0
      have : x = 0 := by simpa using hx
      rw [this, hy]; simp
  have hdenQ : y ^ 2 - x ^ 2 * d ≠ 0 := by exact_mod_cast hden
  refine ⟨-x / (y ^ 2 - x ^ 2 * d), y / (y ^ 2 - x ^ 2 * d), ?_⟩
  have hv0' : (x : ℝ) * l + y ≠ 0 := hv0
  push_cast
  field_simp
  linear_combination (↑x : ℝ) ^ 2 * hl

include hl hirr in
theorem InQ.div {v w : ℝ} (hv : InQ l v) (hw : InQ l w) (hw0 : w ≠ 0) : InQ l (v / w) := by
  rw [div_eq_mul_inv]; exact hv.mul hl (hw.inv hl hirr hw0)

include hl in
/-- An element of `ℚ(l)` is a root of a nonzero rational polynomial of degree at most `2`. -/
theorem InQ.quadratic {v : ℝ} (hv : InQ l v) :
    ∃ P : ℚ[X], P ≠ 0 ∧ P.natDegree ≤ 2 ∧ aeval v P = 0 := by
  obtain ⟨x, y, rfl⟩ := hv
  refine ⟨(X - C y) ^ 2 - C (x ^ 2 * d), ?_, ?_, ?_⟩
  · have hdeg : degree ((X - C y) ^ 2 : ℚ[X]) = 2 := by
      rw [degree_pow, degree_X_sub_C]; rfl
    have hm : ((X - C y) ^ 2 - C (x ^ 2 * d) : ℚ[X]).Monic :=
      ((monic_X_sub_C y).pow 2).sub_of_left (lt_of_le_of_lt degree_C_le (by rw [hdeg]; norm_num))
    exact hm.ne_zero
  · compute_degree
  · simp only [map_sub, map_pow, aeval_X, aeval_C, eq_ratCast]
    push_cast
    linear_combination (↑x ^ 2 : ℝ) * hl

end

end TriangleTiling
