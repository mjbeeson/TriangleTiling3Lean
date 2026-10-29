/-
One-sided covers on the real line.

If the points just to the left of `x` (all but finitely many of them) are covered by finitely many
closed intervals, then one of the intervals contains `x` together with an interval to its left.
Applied along a line through a tiling, this finds the tile edge that reaches a point from a given
direction.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith

namespace TriangleTiling

open Set

variable {ι : Type*}

/-- Finitely many intervals, each either reaching `x` from the left or lying to the left of some
`m < x`: there is a common bound `m`. -/
theorem exists_bound_left (s : Finset ι) (lo hi : ι → ℝ) (x : ℝ) {m₀ : ℝ} (hm₀ : m₀ < x)
    (h : ∀ k ∈ s, lo k < x → hi k < x) :
    ∃ m, m < x ∧ m₀ ≤ m ∧ ∀ k ∈ s, lo k < x → hi k ≤ m := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨m₀, hm₀, le_rfl, fun k hk => absurd hk (Finset.notMem_empty k)⟩
  | insert j s hj ih =>
    obtain ⟨m, hmx, hm0, hm⟩ := ih fun k hk => h k (Finset.mem_insert_of_mem hk)
    by_cases hjx : lo j < x
    · have hj' := h j (Finset.mem_insert_self j s) hjx
      refine ⟨max m (hi j), max_lt hmx hj', le_trans hm0 (le_max_left _ _), ?_⟩
      intro k hk hkx
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact le_max_right _ _
      · exact le_trans (hm k hk hkx) (le_max_left _ _)
    · refine ⟨m, hmx, hm0, ?_⟩
      intro k hk hkx
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact absurd hkx hjx
      · exact hm k hk hkx

/-- Mirror image of `exists_bound_left`. -/
theorem exists_bound_right (s : Finset ι) (lo hi : ι → ℝ) (x : ℝ) {m₀ : ℝ} (hm₀ : x < m₀)
    (h : ∀ k ∈ s, x < hi k → x < lo k) :
    ∃ m, x < m ∧ m ≤ m₀ ∧ ∀ k ∈ s, x < hi k → m ≤ lo k := by
  obtain ⟨m, hmx, hm0, hm⟩ := exists_bound_left s (fun k => -hi k) (fun k => -lo k) (-x)
    (m₀ := -m₀) (by linarith) (fun k hk hkx => by have := h k hk (by linarith); linarith)
  exact ⟨-m, by linarith, by linarith, fun k hk hkx => by have := hm k hk (by linarith); linarith⟩

/-- **One-sided cover, from the left.** If every point of `(x - δ₀, x)` outside a finite set `E`
lies in one of finitely many intervals `[lo k, hi k]`, then some interval satisfies
`lo k < x ≤ hi k`. -/
theorem exists_interval_left (s : Finset ι) (lo hi : ι → ℝ) (x : ℝ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    {E : Set ℝ} (hE : E.Finite)
    (hcov : ∀ y ∈ Ioo (x - δ₀) x, y ∉ E → ∃ k ∈ s, y ∈ Icc (lo k) (hi k)) :
    ∃ k ∈ s, lo k < x ∧ x ≤ hi k := by
  by_contra hno
  push Not at hno
  obtain ⟨m, hmx, hm0, hm⟩ := exists_bound_left s lo hi x (m₀ := x - δ₀) (by linarith) hno
  obtain ⟨y, hy, hyE⟩ := ((Set.Ioo_infinite hmx).diff hE).nonempty
  obtain ⟨k, hk, hyk⟩ := hcov y ⟨by linarith [hy.1], hy.2⟩ hyE
  have := hm k hk (lt_of_le_of_lt hyk.1 hy.2)
  linarith [hy.1, hyk.2]

/-- **One-sided cover, from the right.** -/
theorem exists_interval_right (s : Finset ι) (lo hi : ι → ℝ) (x : ℝ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    {E : Set ℝ} (hE : E.Finite)
    (hcov : ∀ y ∈ Ioo x (x + δ₀), y ∉ E → ∃ k ∈ s, y ∈ Icc (lo k) (hi k)) :
    ∃ k ∈ s, lo k ≤ x ∧ x < hi k := by
  by_contra hno
  push Not at hno
  obtain ⟨m, hmx, hm0, hm⟩ := exists_bound_right s lo hi x (m₀ := x + δ₀) (by linarith)
    (fun k hk hkx => by by_contra h; push Not at h; exact absurd (hno k hk h) (not_le.mpr hkx))
  obtain ⟨y, hy, hyE⟩ := ((Set.Ioo_infinite hmx).diff hE).nonempty
  obtain ⟨k, hk, hyk⟩ := hcov y ⟨hy.1, by linarith [hy.2]⟩ hyE
  have := hm k hk (lt_of_lt_of_le hy.1 hyk.2)
  linarith [hy.2, hyk.1]

end TriangleTiling
