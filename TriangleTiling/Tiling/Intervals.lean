/-
One-dimensional chains of intervals.

If finitely many nondegenerate closed intervals cover `[0, 1]`, lie in it, and pairwise meet in at
most one point, then every right endpoint other than `1` is the left endpoint of another interval.
Consequently the endpoints strictly between `0` and `1` number at most one less than the
intervals. This is the "the `p` tiles supported by `AB` meet at `p - 1` vertices in the interior
of `AB`" step used throughout Beeson's pigeonhole arguments.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

namespace TriangleTiling

open Set

variable {ι : Type*} (s : Finset ι) (l r : ι → ℝ)

/-- The hypotheses: nondegenerate intervals inside `[0,1]`, covering it, pairwise meeting in at
most one point. -/
structure IntervalChain : Prop where
  lt : ∀ k ∈ s, l k < r k
  sub : ∀ k ∈ s, 0 ≤ l k ∧ r k ≤ 1
  cover : ∀ x, 0 ≤ x → x ≤ 1 → ∃ k ∈ s, l k ≤ x ∧ x ≤ r k
  disj : ∀ k ∈ s, ∀ j ∈ s, k ≠ j → (Icc (l k) (r k) ∩ Icc (l j) (r j)).Subsingleton

variable {s l r}

/-- Every right endpoint other than `1` is the left endpoint of another interval. -/
theorem IntervalChain.exists_left_eq_right (h : IntervalChain s l r) {k : ι} (hk : k ∈ s)
    (hr1 : r k ≠ 1) : ∃ j ∈ s, l j = r k := by
  classical
  have hrk : r k < 1 := lt_of_le_of_ne (h.sub k hk).2 hr1
  by_contra hno
  push Not at hno
  -- Some interval `j` reaches past `r k` from at or before `r k`.
  have hstep : ∃ j ∈ s, l j ≤ r k ∧ r k < r j := by
    set T : Finset ℝ := insert 1 ((s.filter fun j => r k < l j).image l) with hT
    have hTne : T.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
    set m := T.min' hTne
    have hmT : ∀ x ∈ T, r k < x := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hrk
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
        exact (Finset.mem_filter.mp hj).2
    have hm : r k < m := hmT m (Finset.min'_mem T hTne)
    have hm1 : m ≤ 1 := Finset.min'_le T 1 (Finset.mem_insert_self _ _)
    have h0 : 0 ≤ r k := (h.sub k hk).1.trans (h.lt k hk).le
    obtain ⟨j, hj, hlj, hrj⟩ := h.cover ((r k + m) / 2) (by linarith) (by linarith)
    refine ⟨j, hj, ?_, by linarith⟩
    by_contra hlt
    push Not at hlt
    have : m ≤ l j := Finset.min'_le T (l j)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hlt⟩, rfl⟩))
    linarith
  obtain ⟨j, hj, hlj, hrj⟩ := hstep
  have hjk : k ≠ j := by rintro rfl; linarith
  have hlj' : l j < r k := lt_of_le_of_ne hlj (hno j hj)
  -- Then the two intervals share `[max (l k) (l j), r k]`, of positive length.
  set M := max (l k) (l j)
  have hM : M < r k := max_lt (h.lt k hk) hlj'
  have hx : r k ∈ Icc (l k) (r k) ∩ Icc (l j) (r j) :=
    ⟨⟨(h.lt k hk).le, le_rfl⟩, ⟨hlj, hrj.le⟩⟩
  have hy : (M + r k) / 2 ∈ Icc (l k) (r k) ∩ Icc (l j) (r j) := by
    refine ⟨⟨?_, by linarith⟩, ⟨?_, by linarith⟩⟩
    · have := le_max_left (l k) (l j); linarith
    · have := le_max_right (l k) (l j); linarith
  have := h.disj k hk j hj hjk hx hy
  linarith

/-- At most one interval ends at `1`. -/
theorem IntervalChain.right_eq_one_unique (h : IntervalChain s l r) {k j : ι} (hk : k ∈ s)
    (hj : j ∈ s) (hrk : r k = 1) (hrj : r j = 1) : k = j := by
  by_contra hkj
  set M := max (l k) (l j)
  have hM : M < 1 := max_lt (hrk ▸ h.lt k hk) (hrj ▸ h.lt j hj)
  have hx : (1 : ℝ) ∈ Icc (l k) (r k) ∩ Icc (l j) (r j) :=
    ⟨⟨by rw [← hrk]; exact (h.lt k hk).le, hrk.ge⟩, ⟨by rw [← hrj]; exact (h.lt j hj).le, hrj.ge⟩⟩
  have hy : (M + 1) / 2 ∈ Icc (l k) (r k) ∩ Icc (l j) (r j) := by
    refine ⟨⟨?_, by linarith⟩, ⟨?_, by linarith⟩⟩
    · have := le_max_left (l k) (l j); linarith
    · have := le_max_right (l k) (l j); linarith
  have := h.disj k hk j hj hkj hx hy
  linarith

/-- At most one interval starts at `0`. -/
theorem IntervalChain.left_eq_zero_unique (h : IntervalChain s l r) {k j : ι} (hk : k ∈ s)
    (hj : j ∈ s) (hlk : l k = 0) (hlj : l j = 0) : k = j := by
  by_contra hkj
  set m := min (r k) (r j)
  have hm : 0 < m := lt_min (hlk ▸ h.lt k hk) (hlj ▸ h.lt j hj)
  have hx : (0 : ℝ) ∈ Icc (l k) (r k) ∩ Icc (l j) (r j) :=
    ⟨⟨hlk.le, by rw [← hlk]; exact (h.lt k hk).le⟩, ⟨hlj.le, by rw [← hlj]; exact (h.lt j hj).le⟩⟩
  have hy : m / 2 ∈ Icc (l k) (r k) ∩ Icc (l j) (r j) := by
    refine ⟨⟨by linarith, ?_⟩, ⟨by linarith, ?_⟩⟩
    · have := min_le_left (r k) (r j); linarith
    · have := min_le_right (r k) (r j); linarith
  have := h.disj k hk j hj hkj hx hy
  linarith

/-- **The endpoint count.** The endpoints strictly between `0` and `1` number at most one less
than the intervals. -/
theorem IntervalChain.card_interior_endpoints [DecidableEq ℝ] (h : IntervalChain s l r) :
    ((s.image l ∪ s.image r).filter fun x => x ≠ 0 ∧ x ≠ 1).card + 1 ≤ s.card := by
  classical
  -- `0` is a left endpoint.
  obtain ⟨k0, hk0, hl0, -⟩ := h.cover 0 le_rfl zero_le_one
  have hl0' : l k0 = 0 := le_antisymm hl0 (h.sub k0 hk0).1
  have h0 : (0 : ℝ) ∈ s.image l := Finset.mem_image.mpr ⟨k0, hk0, hl0'⟩
  -- The interior endpoints are left endpoints other than `0`.
  have hsub : ((s.image l ∪ s.image r).filter fun x => x ≠ 0 ∧ x ≠ 1) ⊆ (s.image l).erase 0 := by
    intro x hx
    obtain ⟨hx, hx0, hx1⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_erase.mpr ⟨hx0, ?_⟩
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hx
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, hj, hjk⟩ := h.exists_left_eq_right hk hx1
      exact Finset.mem_image.mpr ⟨j, hj, hjk⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem h0] at h1
  have h2 : (s.image l).card ≤ s.card := Finset.card_image_le
  have h3 : 0 < (s.image l).card := Finset.card_pos.mpr ⟨0, h0⟩
  omega

end TriangleTiling
