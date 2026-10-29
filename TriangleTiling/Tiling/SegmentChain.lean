/-
Chains of segments covering a segment.

If finitely many nondegenerate segments cover the segment `AB` and pairwise meet in at most one
point, then (i) their endpoints other than `A` and `B` number at most one less than the
segments, and (ii) at most one of them has `B` as an endpoint, and at most one has `A`.

Applied to the tile edges on a side of the tiled triangle (Bonfioli's `side_partition`), this is
the paper's "the `p` tiles supported by `AB` meet at `p - 1` vertices in the interior of `AB`".
-/
import TriangleTiling.Tiling.Intervals
import Mathlib.Analysis.Convex.Segment
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

namespace TriangleTiling

open Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem segment_chain_endpoints [DecidableEq E] {ι : Type*} (A B : E) (hAB : A ≠ B)
    (s : Finset ι) (u v : ι → E) (huv : ∀ k ∈ s, u k ≠ v k)
    (hcov : (⋃ k ∈ s, segment ℝ (u k) (v k)) = segment ℝ A B)
    (hdisj : ∀ k ∈ s, ∀ j ∈ s, k ≠ j →
      (segment ℝ (u k) (v k) ∩ segment ℝ (u j) (v j)).Subsingleton) :
    ((s.image u ∪ s.image v).filter fun x => x ≠ A ∧ x ≠ B).card + 1 ≤ s.card ∧
    (∀ k ∈ s, ∀ j ∈ s, (u k = B ∨ v k = B) → (u j = B ∨ v j = B) → k = j) ∧
    (∀ k ∈ s, ∀ j ∈ s, (u k = A ∨ v k = A) → (u j = A ∨ v j = A) → k = j) := by
  classical
  set L : ℝ →ᵃ[ℝ] E := AffineMap.lineMap A B with hLdef
  have hL : Function.Injective L := AffineMap.lineMap_injective ℝ hAB
  have hL0 : L 0 = A := AffineMap.lineMap_apply_zero A B
  have hL1 : L 1 = B := AffineMap.lineMap_apply_one A B
  have hseg : segment ℝ A B = L '' Icc 0 1 := by
    rw [segment_eq_image_lineMap]
  -- Parameters of the endpoints.
  have hmem : ∀ k ∈ s, u k ∈ segment ℝ A B ∧ v k ∈ segment ℝ A B := by
    intro k hk
    rw [← hcov]
    exact ⟨mem_biUnion hk (left_mem_segment ℝ _ _), mem_biUnion hk (right_mem_segment ℝ _ _)⟩
  have hpar : ∀ x ∈ segment ℝ A B, ∃ t ∈ Icc (0 : ℝ) 1, L t = x := by
    intro x hx; rw [hseg] at hx; exact hx
  let tu : ι → ℝ := fun k =>
    if h : ∃ t ∈ Icc (0 : ℝ) 1, L t = u k then h.choose else 0
  let tv : ι → ℝ := fun k =>
    if h : ∃ t ∈ Icc (0 : ℝ) 1, L t = v k then h.choose else 0
  have htu : ∀ k ∈ s, tu k ∈ Icc (0 : ℝ) 1 ∧ L (tu k) = u k := by
    intro k hk
    have h := hpar _ (hmem k hk).1
    simp only [tu, dif_pos h]
    exact h.choose_spec
  have htv : ∀ k ∈ s, tv k ∈ Icc (0 : ℝ) 1 ∧ L (tv k) = v k := by
    intro k hk
    have h := hpar _ (hmem k hk).2
    simp only [tv, dif_pos h]
    exact h.choose_spec
  let l : ι → ℝ := fun k => min (tu k) (tv k)
  let r : ι → ℝ := fun k => max (tu k) (tv k)
  have hsegk : ∀ k ∈ s, segment ℝ (u k) (v k) = L '' Icc (l k) (r k) := by
    intro k hk
    rw [← (htu k hk).2, ← (htv k hk).2, ← image_segment, segment_eq_Icc']
  have hchain : IntervalChain s l r := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k hk
      have hne : tu k ≠ tv k := fun h => huv k hk (by rw [← (htu k hk).2, ← (htv k hk).2, h])
      exact min_lt_max.mpr hne
    · intro k hk
      exact ⟨le_min (htu k hk).1.1 (htv k hk).1.1, max_le (htu k hk).1.2 (htv k hk).1.2⟩
    · intro x hx0 hx1
      have hLx : L x ∈ segment ℝ A B := by rw [hseg]; exact ⟨x, ⟨hx0, hx1⟩, rfl⟩
      rw [← hcov] at hLx
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hLx
      rw [hsegk k hk] at hxk
      obtain ⟨y, hy, hyx⟩ := hxk
      exact ⟨k, hk, (hL hyx) ▸ hy.1, (hL hyx) ▸ hy.2⟩
    · intro k hk j hj hkj x hx y hy
      have h := hdisj k hk j hj hkj
      have hx' : L x ∈ segment ℝ (u k) (v k) ∩ segment ℝ (u j) (v j) := by
        rw [hsegk k hk, hsegk j hj]
        exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
      have hy' : L y ∈ segment ℝ (u k) (v k) ∩ segment ℝ (u j) (v j) := by
        rw [hsegk k hk, hsegk j hj]
        exact ⟨⟨y, hy.1, rfl⟩, ⟨y, hy.2, rfl⟩⟩
      exact hL (h hx' hy')
  -- Each parameter of an endpoint is the left or right end of its interval.
  have hends : ∀ k ∈ s, ∀ t, (t = tu k ∨ t = tv k) → (t = l k ∨ t = r k) := by
    intro k _ t ht
    rcases le_total (tu k) (tv k) with h | h
    · rcases ht with rfl | rfl
      · exact Or.inl (min_eq_left h).symm
      · exact Or.inr (max_eq_right h).symm
    · rcases ht with rfl | rfl
      · exact Or.inr (max_eq_left h).symm
      · exact Or.inl (min_eq_right h).symm
  refine ⟨?_, ?_, ?_⟩
  · -- The plane endpoints other than `A, B` are images of the interior interval endpoints.
    have hsub : ((s.image u ∪ s.image v).filter fun x => x ≠ A ∧ x ≠ B) ⊆
        ((s.image l ∪ s.image r).filter fun x => x ≠ 0 ∧ x ≠ 1).image L := by
      intro x hx
      obtain ⟨hx, hxA, hxB⟩ := Finset.mem_filter.mp hx
      have : ∃ k ∈ s, ∃ t, (t = tu k ∨ t = tv k) ∧ L t = x := by
        rcases Finset.mem_union.mp hx with hx | hx
        · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
          exact ⟨k, hk, tu k, Or.inl rfl, (htu k hk).2⟩
        · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
          exact ⟨k, hk, tv k, Or.inr rfl, (htv k hk).2⟩
      obtain ⟨k, hk, t, ht, rfl⟩ := this
      refine Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩, rfl⟩
      · rcases hends k hk t ht with h | h
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, hk, h.symm⟩)
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, hk, h.symm⟩)
      · rintro rfl; exact hxA hL0
      · rintro rfl; exact hxB hL1
    have := Finset.card_le_card hsub
    have h2 := Finset.card_image_le (s := (s.image l ∪ s.image r).filter fun x => x ≠ 0 ∧ x ≠ 1)
      (f := L)
    have h3 := hchain.card_interior_endpoints
    omega
  · intro k hk j hj hkB hjB
    have hr : ∀ i ∈ s, (u i = B ∨ v i = B) → r i = 1 := by
      intro i hi hiB
      have ht1 : tu i = 1 ∨ tv i = 1 := by
        rcases hiB with h | h
        · exact Or.inl (hL ((htu i hi).2.trans (h.trans hL1.symm)))
        · exact Or.inr (hL ((htv i hi).2.trans (h.trans hL1.symm)))
      apply le_antisymm (hchain.sub i hi).2
      rcases ht1 with h | h
      · rw [← h]; exact le_max_left _ _
      · rw [← h]; exact le_max_right _ _
    exact hchain.right_eq_one_unique hk hj (hr k hk hkB) (hr j hj hjB)
  · intro k hk j hj hkA hjA
    have hl : ∀ i ∈ s, (u i = A ∨ v i = A) → l i = 0 := by
      intro i hi hiA
      have ht0 : tu i = 0 ∨ tv i = 0 := by
        rcases hiA with h | h
        · exact Or.inl (hL ((htu i hi).2.trans (h.trans hL0.symm)))
        · exact Or.inr (hL ((htv i hi).2.trans (h.trans hL0.symm)))
      apply le_antisymm _ (hchain.sub i hi).1
      rcases ht0 with h | h
      · rw [← h]; exact min_le_left _ _
      · rw [← h]; exact min_le_right _ _
    exact hchain.left_eq_zero_unique hk hj (hl k hk hkA) (hl j hj hjA)

end TriangleTiling
