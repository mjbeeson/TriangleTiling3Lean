/-
The tile with its `γ` at an end `V` of the `c` edge `VW` on the side `AB`, for `lemma:twocs`
(facts (A) and (B) of its proof): when `V` is inside `AB`, a tile on `AB` has its `γ` at `V`, and
its other vertex `X` on `AB` lies beyond `V` (`∠ X V W = π`).
-/
import TriangleTiling.TwoCs.Side
import TriangleTiling.TwoCs.Supp

namespace TriangleTiling.TwoCs

open Erdos634.Geometry EuclideanGeometry Set

/-- Two segments `VX` and `VW` of a line meeting only at `V` lie on opposite sides of `V`. -/
theorem opposite_of_subsingleton {A B V X W : Plane} (hAB : A ≠ B)
    (hV : V ∈ segment ℝ A B) (hX : X ∈ segment ℝ A B) (hW : W ∈ segment ℝ A B)
    (hVX : V ≠ X) (hVW : V ≠ W) (h : (segment ℝ V X ∩ segment ℝ V W).Subsingleton) :
    ∠ X V W = Real.pi := by
  rw [segment_eq_image_lineMap] at hV hX hW
  obtain ⟨v, -, rfl⟩ := hV
  obtain ⟨x, -, rfl⟩ := hX
  obtain ⟨w, -, rfl⟩ := hW
  have hinj := AffineMap.lineMap_injective ℝ hAB
  have hvx : v ≠ x := fun e => hVX (by rw [e])
  have hvw : v ≠ w := fun e => hVW (by rw [e])
  have hmem : ∀ y z t : ℝ, t ∈ Set.uIcc y z →
      AffineMap.lineMap A B t ∈ segment ℝ (AffineMap.lineMap A B y) (AffineMap.lineMap A B z) := by
    intro y z t ht
    rw [← image_segment, segment_eq_uIcc]; exact ⟨t, ht, rfl⟩
  have key : ∀ t, t ∈ Set.uIcc v x → t ∈ Set.uIcc v w → t = v := by
    intro t h1 h2
    have := h ⟨hmem v x t h1, hmem v w t h2⟩
      ⟨hmem v x v Set.left_mem_uIcc, hmem v w v Set.left_mem_uIcc⟩
    exact hinj this
  -- If `x, w` were on the same side of `v`, the segments would share more than `V`.
  have hopp : (x < v ∧ v < w) ∨ (w < v ∧ v < x) := by
    rcases lt_or_gt_of_ne hvx with h1 | h1 <;> rcases lt_or_gt_of_ne hvw with h2 | h2
    · exfalso
      have hm := lt_min h1 h2
      have := key ((v + min x w) / 2)
        (Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith [min_le_left x w]⟩))
        (Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith [min_le_right x w]⟩))
      linarith
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl ⟨h1, h2⟩
    · exfalso
      have hm := max_lt h1 h2
      have := key ((v + max x w) / 2)
        (Set.mem_uIcc.mpr (Or.inr ⟨by linarith [le_max_left x w], by linarith⟩))
        (Set.mem_uIcc.mpr (Or.inr ⟨by linarith [le_max_right x w], by linarith⟩))
      linarith
  have hXW : AffineMap.lineMap A B x ≠ (AffineMap.lineMap A B w : Plane) := fun e => by
    have := hinj e; rcases hopp with h | h <;> linarith
  apply angle_eq_pi_of_mem_openSegment hXW
  rw [← image_openSegment]
  refine ⟨v, ?_, rfl⟩
  rcases hopp with h | h
  · rw [openSegment_eq_Ioo (by linarith)]; exact ⟨h.1, h.2⟩
  · rw [openSegment_symm, openSegment_eq_Ioo (by linarith)]; exact ⟨h.1, h.2⟩

variable {N : ℕ} (D : CongruentDissection N) (hsep : AnglesSep D) (hγ : Real.pi / 2 < tileγ D)
  (hcorner : ∀ k, D.target.localAngle (D.target.pts k) < tileγ D)

include hsep hγ hcorner in
open Classical in
/-- **Facts (A), (B).** If `V` is an end of the only `c` edge `eT` on `AB`, `W` its other end, and
`V` is not a corner, then some tile has its `γ` at `V`, and its other vertex `X` on `AB` satisfies
`∠ X V W = π`. -/
theorem side_data (part : Finset (Fin N × Fin 3))
    (hcov : (⋃ e ∈ part, (D.tile e.1).edge e.2) =
      segment ℝ (D.target.pts 0) (D.target.pts 1))
    (hdisj : ∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ →
      ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton)
    (eT : Fin N × Fin 3)
    (heT : part.filter (fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
      = tileγ D) = {eT})
    {V W : Plane}
    (hVW : ((D.tile eT.1).pts eT.2 = V ∧ (D.tile eT.1).pts (eT.2 + 1) = W) ∨
      ((D.tile eT.1).pts eT.2 = W ∧ (D.tile eT.1).pts (eT.2 + 1) = V))
    (hVA : V ≠ D.target.pts 0) (hVB : V ≠ D.target.pts 1) :
    ∃ (T₀ : Fin N) (jV jX : Fin 3), jX ≠ jV ∧ (D.tile T₀).pts jV = V ∧
      (D.tile T₀).localAngle V = tileγ D ∧
      (D.tile T₀).pts jX ∈ segment ℝ (D.target.pts 0) (D.target.pts 1) ∧
      ∠ ((D.tile T₀).pts jX) V W = Real.pi := by
  have heTp : eT ∈ part := by
    have : eT ∈ part.filter (fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
        = tileγ D) := by rw [heT]; exact Finset.mem_singleton_self _
    exact (Finset.mem_filter.mp this).1
  have hsub : ∀ e ∈ part, (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 0) (D.target.pts 1) :=
    fun e he y hy => by rw [← hcov]; exact Set.mem_biUnion he hy
  have hVmem : V ∈ (part.image (fun e => (D.tile e.1).pts e.2) ∪
      part.image (fun e => (D.tile e.1).pts (e.2 + 1))) := by
    rcases hVW with ⟨h, -⟩ | ⟨-, h⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨eT, heTp, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨eT, heTp, h⟩)
  obtain ⟨e₀, he₀, hne, hend, hγV⟩ :=
    side_step D hsep hγ hcorner part hcov hdisj eT heT hVmem hVA hVB
  have hAB : D.target.pts 0 ≠ D.target.pts 1 := D.target.indep.injective.ne (by decide)
  -- The vertex of `T₀` at `V`, and the other end `X` of its edge.
  obtain ⟨jV, jX, hjV, hjX, hjne, hedge⟩ : ∃ jV jX : Fin 3, (D.tile e₀.1).pts jV = V ∧
      jX ≠ jV ∧ True ∧ (D.tile e₀.1).edge e₀.2 = segment ℝ V ((D.tile e₀.1).pts jX) := by
    rcases hend with h | h
    · exact ⟨e₀.2, e₀.2 + 1, h, (fin3_ne_add_one _).symm, trivial, by rw [Tri.edge, h]⟩
    · exact ⟨e₀.2 + 1, e₀.2, h, fin3_ne_add_one _, trivial,
        by rw [Tri.edge, h, segment_symm]⟩
  refine ⟨e₀.1, jV, jX, hjX, hjV, hγV, ?_, ?_⟩
  · apply hsub e₀ he₀; rw [hedge]; exact right_mem_segment _ _ _
  · have heTedge : (D.tile eT.1).edge eT.2 = segment ℝ V W := by
      rcases hVW with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [Tri.edge, h1, h2]
      · rw [Tri.edge, h1, h2, segment_symm]
    have hVX : V ≠ (D.tile e₀.1).pts jX := by
      rw [← hjV]; exact fun h => hjX ((D.tile e₀.1).indep.injective h).symm
    have hVW' : V ≠ W := by
      rcases hVW with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]; exact tri_pts_succ_ne _ _
      · rw [← h1, ← h2]; exact (tri_pts_succ_ne _ _).symm
    have hsub₀ := hsub e₀ he₀
    have hsubT := hsub eT heTp
    rw [hedge] at hsub₀
    rw [heTedge] at hsubT
    apply opposite_of_subsingleton hAB (hsubT (left_mem_segment _ _ _))
      (hsub₀ (right_mem_segment _ _ _)) (hsubT (right_mem_segment _ _ _)) hVX hVW'
    have := hdisj e₀ he₀ eT heTp hne
    rwa [hedge, heTedge] at this

end TriangleTiling.TwoCs
