/-
Chords: segments joining two boundary points of the tiled triangle.

If `P` and `Q` are boundary points of a convex closed set `K` and the open segment between them
runs through the interior of `K`, then the line `PQ` meets `K` exactly in the segment `PQ`.

Applied to a tile edge whose two ends lie on the boundary of the tiled triangle: the tile edges on
each side of it lie within it, and their lengths add up to its length (via Bonfioli's
`Dissection.edge_two_sided`).
-/
import Erdos634.WallChain
import TriangleTiling.Tiling.Intervals

namespace TriangleTiling

open Erdos634.Geometry MeasureTheory Set

/-- **The chord lemma, in parameters.** If `P, Q` are not interior to the convex set `K`,
the midpoint of `PQ` is interior, and `lineMap P Q t ∈ K`, then `0 ≤ t ≤ 1`. -/
theorem chord_param {K : Set Plane} (hK : Convex ℝ K) {P Q : Plane}
    (hP : P ∉ interior K) (hQ : Q ∉ interior K)
    (hm : AffineMap.lineMap P Q (1 / 2 : ℝ) ∈ interior K) {t : ℝ}
    (ht : AffineMap.lineMap P Q t ∈ K) : t ∈ Icc (0 : ℝ) 1 := by
  set L : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap P Q
  have hcl : L t ∈ closure K := subset_closure ht
  have hsub := hK.openSegment_interior_closure_subset_interior hm hcl
  rw [← image_openSegment] at hsub
  refine ⟨?_, ?_⟩
  · by_contra h
    push Not at h
    apply hP
    have : P = L 0 := (AffineMap.lineMap_apply_zero P Q).symm
    rw [this]
    apply hsub
    refine ⟨0, ?_, rfl⟩
    rw [openSegment_symm, openSegment_eq_Ioo (by linarith)]
    exact ⟨h, by norm_num⟩
  · by_contra h
    push Not at h
    apply hQ
    have : Q = L 1 := (AffineMap.lineMap_apply_one P Q).symm
    rw [this]
    apply hsub
    refine ⟨1, ?_, rfl⟩
    rw [openSegment_eq_Ioo (by linarith)]
    exact ⟨by norm_num, h⟩

/-- A point on the level line `{f = c}` through two distinct points `P, Q` of it is
`lineMap P Q t` for some `t`. -/
theorem eq_lineMap_of_level {f : Plane →ₗ[ℝ] ℝ} (hf : f ≠ 0) {c : ℝ} {P Q y : Plane}
    (hPQ : P ≠ Q) (hP : f P = c) (hQ : f Q = c) (hy : f y = c) :
    ∃ t : ℝ, y = AffineMap.lineMap P Q t := by
  have hn := rotVec_ne_zero hf
  have hu : cross (rotVec f) (Q - P) = 0 := by rw [← rotVec_spec, map_sub, hP, hQ, sub_self]
  have hv : cross (rotVec f) (y - P) = 0 := by rw [← rotVec_spec, map_sub, hP, hy, sub_self]
  have hcr := cross_eq_zero_of_common_ker hn hu hv
  obtain ⟨τ, hτ⟩ := parallel_of_cross_eq_zero (sub_ne_zero.mpr hPQ.symm) hcr
  refine ⟨τ, ?_⟩
  rw [AffineMap.lineMap_apply_module', ← hτ]
  abel

/-- **The chord lemma.** If `P, Q` are not interior to the convex set `K`, the midpoint of
`PQ` is interior, and `f` is a nonzero functional constant on `PQ`, then every point of `K` on
the line `{f = f P}` lies on the segment `PQ`. -/
theorem chord_mem_segment {K : Set Plane} (hK : Convex ℝ K) {P Q : Plane}
    (hPQ : P ≠ Q) (hP : P ∉ interior K) (hQ : Q ∉ interior K)
    (hm : AffineMap.lineMap P Q (1 / 2 : ℝ) ∈ interior K)
    {f : Plane →ₗ[ℝ] ℝ} (hf : f ≠ 0) {c : ℝ} (hfP : f P = c) (hfQ : f Q = c)
    {y : Plane} (hy : y ∈ K) (hfy : f y = c) : y ∈ segment ℝ P Q := by
  obtain ⟨t, rfl⟩ := eq_lineMap_of_level hf hPQ hfP hfQ hfy
  rw [segment_eq_image_lineMap]
  exact ⟨t, chord_param hK hP hQ hm hy, rfl⟩

/-- **Both sides of a chord edge.** Let edge `k` of tile `j` join two points `P, Q` that are not
interior to the tiled triangle, while its interior lies inside. Then there is a nonzero functional
`f`, constant `= c` on the edge, such that the tile edges on the line on either side (Bonfioli's
`lineChain f c` and `lineChain (-f) (-c)`) lie in the segment `PQ`, and on each side their lengths
add up to `|PQ|`. -/
theorem chord_two_sided {N : ℕ} (D : Dissection N) (j : Fin N) (k : Fin 3)
    (hP : (D.tile j).pts k ∉ interior D.target.carrier)
    (hQ : (D.tile j).pts (k + 1) ∉ interior D.target.carrier)
    (hint : openSegment ℝ ((D.tile j).pts k) ((D.tile j).pts (k + 1))
      ⊆ interior D.target.carrier) :
    ∃ (f : Plane →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧ (∀ y ∈ (D.tile j).edge k, f y = c) ∧
      (∀ e ∈ D.lineChain f c ∪ D.lineChain (-f) (-c),
        (D.tile e.1).edge e.2 ⊆ (D.tile j).edge k) ∧
      (∑ e ∈ D.lineChain f c, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
        = dist ((D.tile j).pts k) ((D.tile j).pts (k + 1))) ∧
      (∑ e ∈ D.lineChain (-f) (-c), dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
        = dist ((D.tile j).pts k) ((D.tile j).pts (k + 1))) := by
  classical
  obtain ⟨f, c, hf, hline, hnear, hfar⟩ := D.edge_two_sided j k hint
  set P := (D.tile j).pts k
  set Q := (D.tile j).pts (k + 1)
  have hPQ : P ≠ Q := (D.tile j).indep.injective.ne (by fin_cases k <;> decide)
  have hfP : f P = c := hline P (left_mem_segment _ _ _)
  have hfQ : f Q = c := hline Q (right_mem_segment _ _ _)
  have hm : AffineMap.lineMap P Q (1 / 2 : ℝ) ∈ interior D.target.carrier := by
    apply hint
    rw [openSegment_eq_image_lineMap]
    exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
  have htile : ∀ i, (D.tile i).carrier ⊆ D.target.carrier := fun i z hz => by
    rw [← D.covers]; exact mem_iUnion.mpr ⟨i, hz⟩
  have hvert : ∀ (i : Fin N) (m : Fin 3), (D.tile i).pts m ∈ D.target.carrier :=
    fun i m => htile i (subset_convexHull ℝ _ ⟨m, rfl⟩)
  -- Chain edges lie in `PQ`.
  have hsub : ∀ e ∈ D.lineChain f c ∪ D.lineChain (-f) (-c),
      (D.tile e.1).edge e.2 ⊆ (D.tile j).edge k := by
    intro e he
    have hends : f ((D.tile e.1).pts e.2) = c ∧ f ((D.tile e.1).pts (e.2 + 1)) = c := by
      rcases Finset.mem_union.mp he with h | h
      · obtain ⟨h1, h2, -⟩ := Dissection.mem_lineChain.mp h
        exact ⟨h1, h2⟩
      · obtain ⟨h1, h2, -⟩ := Dissection.mem_lineChain.mp h
        simp only [LinearMap.neg_apply, neg_inj] at h1 h2
        exact ⟨h1, h2⟩
    have hu := chord_mem_segment D.target.convex hPQ hP hQ hm hf
      hfP hfQ (hvert _ _) hends.1
    have hv := chord_mem_segment D.target.convex hPQ hP hQ hm hf
      hfP hfQ (hvert _ _) hends.2
    exact (convex_segment (𝕜 := ℝ) P Q).segment_subset hu hv
  refine ⟨f, c, hf, hline, hsub, ?_, ?_⟩
  · -- near side
    have hs' : ∑ e ∈ D.lineChain f c, edist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
        = edist P Q := by
      rw [← (D.tile j).hausdorff_edge k, ← hnear]
      refine Finset.sum_congr rfl fun e he => ?_
      rw [Set.inter_eq_left.mpr (hsub e (Finset.mem_union_left _ he)), Tri.hausdorff_edge]
    have := congrArg ENNReal.toReal hs'
    rw [ENNReal.toReal_sum (fun e _ => edist_ne_top _ _)] at this
    simpa [← dist_edist] using this
  · -- far side
    have hs' : ∑ e ∈ D.lineChain (-f) (-c),
        edist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = edist P Q := by
      rw [← (D.tile j).hausdorff_edge k, ← hfar]
      refine Finset.sum_congr rfl fun e he => ?_
      rw [Set.inter_eq_left.mpr (hsub e (Finset.mem_union_right _ he)), Tri.hausdorff_edge]
    have := congrArg ENNReal.toReal hs'
    rw [ENNReal.toReal_sum (fun e _ => edist_ne_top _ _)] at this
    simpa [← dist_edist] using this

end TriangleTiling
