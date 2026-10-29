/-
Out of a center (the step "every center has an outgoing link" of `lemma:abrelation` and
`lemma:essentialsegments`), for any class of marked edges.

At an interior point `Q` lying inside no tile edge, where the marked edges are odd in number and
no set of tiles has angles adding up to `π` at `Q`, a link leaves `Q`, unless there is a relation.
This is `center_out` (`GammaVertices.lean`) with its hypotheses made explicit.
-/
import TriangleTiling.Isosceles.GammaVertices

namespace TriangleTiling

open Erdos634.Geometry Set

variable {N : ℕ} (D : Dissection N) (isθ : Fin N × Fin 3 → Prop)

open Classical in
/-- **Out of a center**: a link leaves `Q`, unless there is a relation. -/
theorem out_of_center {Q : Plane} (hQint : Q ∈ interior D.target.carrier)
    (hnrel : ∀ j : Fin N, ∀ m : Fin 3,
      Q ∉ openSegment ℝ ((D.tile j).pts m) ((D.tile j).pts (m + 1)))
    (hodd : Odd ((edgesAt D Q).filter isθ).card)
    (hnohalf : ∀ S : Finset (Fin N), ∑ i ∈ S, (D.tile i).localAngle Q ≠ Real.pi)
    (hnorel : ¬ HasRelation D isθ) :
    ∃ R, IsLink D isθ Q R := by
  classical
  -- No edge is alone on its ray.
  have hnolone : ∀ e ∈ edgesAt D Q, ∃ e' ∈ edgesAt D Q,
      Partners D Q e e' := by
    intro e he
    by_contra hno
    push Not at hno
    obtain ⟨-, -, -, -, -, -, e₂, -, hQe₂⟩ := lonely_relint D hQint he
      (fun e' he' hne hray => hno e' he' ⟨hne.symm, hray⟩)
    exact hnrel _ _ hQe₂
  -- An odd number of marked edges: a mixed ray.
  obtain ⟨x, hx, y, hy, hxy, hθx, hθy⟩ : ∃ x ∈ edgesAt D Q,
      ∃ y ∈ edgesAt D Q, Partners D Q x y ∧
        isθ x ∧ ¬ isθ y := by
    by_contra hno
    push Not at hno
    have hpar := card_filter_mod_two (edgesAt D Q) (Partners D Q)
      (isθ) (fun x _ y _ h => ⟨h.1.symm, sameRayAt_symm _ h.2⟩)
      (fun x h => h.1 rfl)
      (fun x hx y hy z hz hxy hxz => by
        by_contra hyz
        exact sameRayAt_unique _ hx hy hz hxy.1.symm hxz.1.symm hyz hxy.2 hxz.2)
      (fun x hx y hy hxy hθ => hno x hx y hy hxy hθ) ∅ (fun x => by
        simp only [Finset.notMem_empty, false_iff, not_and, not_forall, not_not]
        intro hx _
        obtain ⟨e', he', h'⟩ := hnolone x hx
        exact ⟨e', he', h'⟩)
    rw [Finset.card_empty] at hpar
    obtain ⟨k, hk⟩ := hodd
    omega
  -- Nothing runs backwards from the center along that ray.
  have hback : ∀ e : Fin N × Fin 3, Q ∈ (D.tile e.1).edge e.2 →
      ∀ z ∈ (D.tile e.1).edge e.2, Q ∉ openSegment ℝ z (farEnd D Q x) := by
    intro e hQe z hz hQz
    set F := farEnd D Q x
    have hQF : Q ≠ F := (farEnd_ne _ hx).symm
    -- `Q` is an end of `e`.
    have he : e ∈ edgesAt D Q := by
      rw [Tri.edge, ← insert_endpoints_openSegment] at hQe
      rcases hQe with h | h | h
      · exact (mem_edgesAt _).mpr (Or.inl h.symm)
      · exact (mem_edgesAt _).mpr (Or.inr h.symm)
      · exact absurd h (hnrel e.1 e.2)
    obtain ⟨g, c, hg, hgQ, hgF⟩ := ray_level (farEnd_ne _ hx)
    -- `z` is on the line, behind `Q`.
    have hgz : g z = c := by
      obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hQz
      have h1 := hgQ
      rw [← hcomb, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hgF] at h1
      have : a * (g z - c) = 0 := by linear_combination h1 - c * hab
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    obtain ⟨tz, htz⟩ := eq_lineMap_of_level hg hQF hgQ hgF hgz
    have htz0 : tz < 0 := by
      have h0 : AffineMap.lineMap Q F (0 : ℝ) ∈
          openSegment ℝ (AffineMap.lineMap Q F tz) (AffineMap.lineMap Q F (1 : ℝ)) := by
        rw [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, ← htz]; exact hQz
      rw [← image_openSegment, (AffineMap.lineMap_injective ℝ hQF).mem_set_image] at h0
      rcases lt_trichotomy tz 1 with h | h | h
      · rw [openSegment_eq_Ioo h] at h0; exact h0.1
      · rw [h, openSegment_same] at h0; norm_num at h0
      · rw [openSegment_symm, openSegment_eq_Ioo h] at h0; linarith [h0.1]
    -- The far end of `e` is on the line, behind `Q`.
    have hzQ : z ≠ Q := by
      intro h
      have : AffineMap.lineMap Q F tz = AffineMap.lineMap Q F (0 : ℝ) := by
        rw [← htz, h, AffineMap.lineMap_apply_zero]
      exact htz0.ne (AffineMap.lineMap_injective ℝ hQF this)
    rw [edgesAt_edge _ he, segment_eq_image_lineMap] at hz
    obtain ⟨s, hs, hzs⟩ := hz
    have hs0 : 0 < s := by
      rcases hs.1.lt_or_eq with h | h
      · exact h
      · rw [← h, AffineMap.lineMap_apply_zero] at hzs; exact absurd hzs.symm hzQ
    have hgfe : g (farEnd D Q e) = c := by
      have := congrArg g hzs
      rw [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul, hgQ, hgz]
        at this
      have h' : s * (g (farEnd D Q e) - c) = 0 := by linarith
      rcases mul_eq_zero.mp h' with h | h
      · linarith
      · linarith
    obtain ⟨te, hte⟩ := eq_lineMap_of_level hg hQF hgQ hgF hgfe
    have hte0 : te < 0 := by
      rw [hte, lineMap_lineMap_eq, htz] at hzs
      have := AffineMap.lineMap_injective ℝ hQF hzs
      nlinarith
    obtain ⟨S, hS⟩ := straight_angle_sum D hQint hx he hte0 hte
    exact hnohalf S hS
  rcases extend_link D (isθ) hx hy hxy.1.symm hxy.2 hθx hθy
    hback with h | h
  · exact h
  · exact absurd h hnorel

end TriangleTiling
