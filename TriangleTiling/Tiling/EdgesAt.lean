/-
The edges of a tiling at a point.

The tile edges with an end at `Q` run along rays from `Q`. Along any ray there are at most two of
them, one on each side; if only one, then `Q` lies inside an edge of another tile on the same line,
or the ray leaves the interior of the target. With this, a parity count: if no ray carries a
marked edge together with an unmarked one, the number of marked edges at `Q` has the parity of
the number of marked edges alone on their rays.
-/
import TriangleTiling.Tiling.LineParams
import TriangleTiling.Tiling.AngleFacts

namespace TriangleTiling

open Erdos634.Geometry Set

/-! ### Parity of a pairing -/

section Parity

variable {α : Type*} [DecidableEq α]

/-- A finite set paired off by a symmetric relation with unique partners has even size. -/
theorem even_card_of_pairing (R : α → α → Prop) (hsymm : ∀ x y, R x y → R y x)
    (hirr : ∀ x, ¬ R x x) (huniq : ∀ x y z, R x y → R x z → y = z) :
    ∀ n (A : Finset α), A.card = n → (∀ x ∈ A, ∃ y ∈ A, R x y) → Even n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hA hpair
  rcases A.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · rw [← hA, Finset.card_empty]; exact ⟨0, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hpair x hx
  have hne : y ≠ x := fun h => hirr x (h ▸ hxy)
  set A' := (A.erase x).erase y with hA'def
  have hcard : A'.card + 2 = n := by
    rw [hA'def, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne, hy⟩),
      Finset.card_erase_of_mem hx, ← hA]
    have : 2 ≤ A.card := by
      have h2 : ({x, y} : Finset α) ⊆ A := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hx
        · rw [Finset.mem_singleton.mp hz]; exact hy
      have := Finset.card_le_card h2
      rwa [Finset.card_pair hne.symm] at this
    omega
  have hpair' : ∀ z ∈ A', ∃ w ∈ A', R z w := by
    intro z hz
    have hzy : z ≠ y := (Finset.mem_erase.mp hz).1
    have hzx : z ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1
    have hzA : z ∈ A := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2
    obtain ⟨w, hw, hzw⟩ := hpair z hzA
    refine ⟨w, ?_, hzw⟩
    have hwx : w ≠ x := by
      rintro rfl
      exact hzy (huniq w y z hxy (hsymm z w hzw)).symm
    have hwy : w ≠ y := by
      rintro rfl
      exact hzx (huniq w x z (hsymm x w hxy) (hsymm z w hzw)).symm
    exact Finset.mem_erase.mpr ⟨hwy, Finset.mem_erase.mpr ⟨hwx, hw⟩⟩
  have := ih A'.card (by omega) A' rfl hpair'
  rw [← hcard]
  exact this.add ⟨1, rfl⟩

/-- **The parity count.** Let `R` pair elements of `S` (symmetric, irreflexive, unique partners in
`S`), and suppose no element of a marked set `Θ` has an unmarked partner. Then the number of marked
elements has the parity of the number of marked elements without a partner (the set `L`). -/
theorem card_filter_mod_two (S : Finset α) (R : α → α → Prop) [DecidableRel R]
    (Θ : α → Prop) [DecidablePred Θ]
    (hsymm : ∀ x ∈ S, ∀ y ∈ S, R x y → R y x) (hirr : ∀ x, ¬ R x x)
    (huniq : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, R x y → R x z → y = z)
    (hnomix : ∀ x ∈ S, ∀ y ∈ S, R x y → Θ x → Θ y)
    (L : Finset α) (hL : ∀ x, x ∈ L ↔ x ∈ S ∧ Θ x ∧ ∀ y ∈ S, ¬ R x y) :
    (S.filter Θ).card % 2 = L.card % 2 := by
  have hLeq : L = S.filter fun x => Θ x ∧ ∀ y ∈ S, ¬ R x y := by
    ext x; rw [hL, Finset.mem_filter]
  subst hLeq
  set P := S.filter fun x => Θ x ∧ ∃ y ∈ S, R x y
  have hsplit : (S.filter Θ).card
      = (S.filter fun x => Θ x ∧ ∀ y ∈ S, ¬ R x y).card + P.card := by
    rw [← Finset.card_filter_add_card_filter_not (s := S.filter Θ) (fun x => ∀ y ∈ S, ¬ R x y),
      Finset.filter_filter, Finset.filter_filter]
    congr 2
    ext x
    simp only [P, Finset.mem_filter, not_forall, not_not, exists_prop]
  -- `R` restricted to `S` pairs off `P`.
  let R' : α → α → Prop := fun x y => x ∈ S ∧ y ∈ S ∧ R x y
  have hP : Even P.card := by
    refine even_card_of_pairing R' (fun x y h => ⟨h.2.1, h.1, hsymm x h.1 y h.2.1 h.2.2⟩)
      (fun x h => hirr x h.2.2)
      (fun x y z h1 h2 => huniq x h1.1 y h1.2.1 z h2.2.1 h1.2.2 h2.2.2) _ P rfl ?_
    intro x hx
    obtain ⟨hxS, hxΘ, y, hyS, hxy⟩ := Finset.mem_filter.mp hx
    refine ⟨y, Finset.mem_filter.mpr ⟨hyS, hnomix x hxS y hyS hxy hxΘ, x, hxS,
      hsymm x hxS y hyS hxy⟩, hxS, hyS, hxy⟩
  rw [hsplit, Nat.add_mod, Nat.even_iff.mp hP, add_zero, Nat.mod_mod]

end Parity

/-! ### Edges at a point -/

section EdgesAt

variable {N : ℕ} (D : Dissection N)

open Classical in
/-- The tile edges with an end at `Q`. -/
noncomputable def edgesAt (Q : Plane) : Finset (Fin N × Fin 3) :=
  Finset.univ.filter fun e => (D.tile e.1).pts e.2 = Q ∨ (D.tile e.1).pts (e.2 + 1) = Q

open Classical in
/-- The other end of an edge at `Q`. -/
noncomputable def farEnd (Q : Plane) (e : Fin N × Fin 3) : Plane :=
  if (D.tile e.1).pts e.2 = Q then (D.tile e.1).pts (e.2 + 1) else (D.tile e.1).pts e.2

/-- Two edges at `Q` along the same ray from `Q`. -/
def SameRayAt (Q : Plane) (e e' : Fin N × Fin 3) : Prop :=
  ∃ t : ℝ, 0 < t ∧ farEnd D Q e' = AffineMap.lineMap Q (farEnd D Q e) t

theorem mem_edgesAt {Q : Plane} {e : Fin N × Fin 3} :
    e ∈ edgesAt D Q ↔ (D.tile e.1).pts e.2 = Q ∨ (D.tile e.1).pts (e.2 + 1) = Q := by
  classical
  simp [edgesAt]

theorem tri_pts_succ_ne (T : Tri) (k : Fin 3) : T.pts k ≠ T.pts (k + 1) := by
  intro h
  have := T.indep.injective h
  have hne : ∀ m : Fin 3, m ≠ m + 1 := by decide
  exact hne k this

/-- The two ends of an edge at `Q` are `Q` and its far end. -/
theorem edgesAt_ends {Q : Plane} {e : Fin N × Fin 3} (he : e ∈ edgesAt D Q) :
    ((D.tile e.1).pts e.2 = Q ∧ (D.tile e.1).pts (e.2 + 1) = farEnd D Q e) ∨
    ((D.tile e.1).pts e.2 = farEnd D Q e ∧ (D.tile e.1).pts (e.2 + 1) = Q) := by
  classical
  rcases (mem_edgesAt D).mp he with h | h
  · left; exact ⟨h, by rw [farEnd, if_pos h]⟩
  · right
    have h' : (D.tile e.1).pts e.2 ≠ Q := fun h0 =>
      tri_pts_succ_ne (D.tile e.1) e.2 (h0.trans h.symm)
    exact ⟨by rw [farEnd, if_neg h'], h⟩

theorem farEnd_ne {Q : Plane} {e : Fin N × Fin 3} (he : e ∈ edgesAt D Q) : farEnd D Q e ≠ Q := by
  rcases edgesAt_ends D he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h2, ← h1]; exact (tri_pts_succ_ne _ _).symm
  · rw [← h1, ← h2]; exact tri_pts_succ_ne _ _

/-- An edge at `Q` is the segment from `Q` to its far end. -/
theorem edgesAt_edge {Q : Plane} {e : Fin N × Fin 3} (he : e ∈ edgesAt D Q) :
    (D.tile e.1).edge e.2 = segment ℝ Q (farEnd D Q e) := by
  rw [Tri.edge]
  rcases edgesAt_ends D he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, segment_symm]

/-- The level line through an edge at `Q`. -/
theorem level_far {Q : Plane} {e : Fin N × Fin 3} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}
    (he : e ∈ edgesAt D Q) (hQ : g Q = c) (hF : g (farEnd D Q e) = c) :
    g ((D.tile e.1).pts e.2) = c ∧ g ((D.tile e.1).pts (e.2 + 1)) = c := by
  rcases edgesAt_ends D he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact ⟨hQ, hF⟩
  · rw [h1, h2]; exact ⟨hF, hQ⟩

/-- No edge lies in both chains of a line: its tile would be flat. -/
theorem not_mem_both_chains {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) {e : Fin N × Fin 3}
    (h1 : e ∈ D.lineChain g c) (h2 : e ∈ D.lineChain (-g) (-c)) : False := by
  obtain ⟨a1, a2, a3⟩ := Dissection.mem_lineChain.mp h1
  obtain ⟨-, -, b3⟩ := Dissection.mem_lineChain.mp h2
  have h3 : g ((D.tile e.1).pts (e.2 + 2)) = c := by
    have := b3 (e.2 + 2)
    simp only [LinearMap.neg_apply, neg_le_neg_iff] at this
    exact le_antisymm (a3 _) this
  obtain ⟨t, ht⟩ := eq_lineMap_of_level hg (tri_pts_succ_ne (D.tile e.1) e.2) a1 a2 h3
  have hc := congrArg ((D.tile e.1).basis.coord (e.2 + 2)) ht
  rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex, Tri.coord_vertex] at hc
  have n1 : ∀ k : Fin 3, ¬ (k + 2 = k) := by decide
  have n2 : ∀ k : Fin 3, ¬ (k + 2 = k + 1) := by decide
  simp [n1 e.2, n2 e.2] at hc

/-- An edge at `Q` lies in one of the two chains of its line. -/
theorem edgesAt_chain {Q : Plane} {e : Fin N × Fin 3} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}
    (he : e ∈ edgesAt D Q) (hQ : g Q = c) (hF : g (farEnd D Q e) = c) :
    e ∈ D.lineChain g c ∨ e ∈ D.lineChain (-g) (-c) := by
  obtain ⟨a1, a2⟩ := level_far D he hQ hF
  rcases le_total (g ((D.tile e.1).pts (e.2 + 2))) c with h | h
  · left
    refine Dissection.mem_lineChain.mpr ⟨a1, a2, fun i => ?_⟩
    rcases fin3_cases3 i e.2 with rfl | rfl | rfl
    · exact a1.le
    · exact a2.le
    · exact h
  · right
    refine Dissection.mem_lineChain.mpr ⟨by simp [a1], by simp [a2], fun i => ?_⟩
    simp only [LinearMap.neg_apply, neg_le_neg_iff]
    rcases fin3_cases3 i e.2 with rfl | rfl | rfl
    · exact a1.ge
    · exact a2.ge
    · exact h

/-! ### The line of a ray -/

/-- The line through `Q` and `F`, as a level set. -/
theorem ray_level {Q F : Plane} (hQF : F ≠ Q) :
    ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ), g ≠ 0 ∧ g Q = c ∧ g F = c := by
  refine ⟨crossL (F - Q), cross (F - Q) Q, crossL_ne_zero (sub_ne_zero.mpr hQF), rfl, ?_⟩
  rw [crossL_apply]
  have h := cross_sub_right (F - Q) F Q
  rw [cross_self] at h
  linarith

/-- Points along the ray of an edge at `Q` lie on the edge. -/
theorem mem_edge_of_ray {Q F : Plane} {e : Fin N × Fin 3} (he : e ∈ edgesAt D Q) {t : ℝ}
    (hF : farEnd D Q e = AffineMap.lineMap Q F t) {s : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) :
    AffineMap.lineMap Q F s ∈ (D.tile e.1).edge e.2 := by
  rw [edgesAt_edge D he, hF]
  have h0 : AffineMap.lineMap Q F (0 : ℝ) = Q := AffineMap.lineMap_apply_zero Q F
  have : segment ℝ Q (AffineMap.lineMap Q F t) = AffineMap.lineMap Q F '' segment ℝ 0 t := by
    rw [image_segment, h0]
  rw [this, segment_eq_Icc (hs0.trans hst)]
  exact ⟨s, ⟨hs0, hst⟩, rfl⟩

theorem lineMap_lineMap_eq {Q F : Plane} (t s : ℝ) :
    AffineMap.lineMap Q (AffineMap.lineMap Q F t) s = AffineMap.lineMap Q F (s * t) := by
  simp only [AffineMap.lineMap_apply_module', smul_smul, add_sub_cancel_right]

/-- Sharing a ray is symmetric. -/
theorem sameRayAt_symm {Q : Plane} {e e' : Fin N × Fin 3} (h : SameRayAt D Q e e') : SameRayAt D Q e' e := by
  obtain ⟨t, ht, hF⟩ := h
  refine ⟨t⁻¹, inv_pos.mpr ht, ?_⟩
  rw [hF, lineMap_lineMap_eq, inv_mul_cancel₀ ht.ne', AffineMap.lineMap_apply_one]

/-- **At most two edges along a ray.** Two edges at `Q` sharing the ray of a third edge, all
three distinct, cannot exist: two of them would lie on the same side of the line and overlap. -/
theorem sameRayAt_unique {Q : Plane} {e e' e'' : Fin N × Fin 3} (he : e ∈ edgesAt D Q)
    (he' : e' ∈ edgesAt D Q) (he'' : e'' ∈ edgesAt D Q) (h1 : e' ≠ e) (h2 : e'' ≠ e)
    (h3 : e' ≠ e'') (r1 : SameRayAt D Q e e') (r2 : SameRayAt D Q e e'') : False := by
  obtain ⟨t', ht', hF'⟩ := r1
  obtain ⟨t'', ht'', hF''⟩ := r2
  set F := farEnd D Q e
  obtain ⟨g, c, hg, hgQ, hgF⟩ := ray_level (farEnd_ne D he)
  set s := min 1 (min t' t'') with hsdef
  have hs : 0 < s := lt_min one_pos (lt_min ht' ht'')
  have hy : ∀ x ∈ edgesAt D Q, ∀ t : ℝ, s ≤ t → farEnd D Q x = AffineMap.lineMap Q F t →
      Q ∈ (D.tile x.1).edge x.2 ∧ AffineMap.lineMap Q F s ∈ (D.tile x.1).edge x.2 := by
    intro x hx t hst ht
    refine ⟨?_, mem_edge_of_ray D hx ht hs.le hst⟩
    rw [edgesAt_edge D hx]; exact left_mem_segment ℝ _ _
  have y0 := hy e he 1 (min_le_left _ _) (AffineMap.lineMap_apply_one Q F).symm
  have y1 := hy e' he' t' ((min_le_right _ _).trans (min_le_left _ _)) hF'
  have y2 := hy e'' he'' t'' ((min_le_right _ _).trans (min_le_right _ _)) hF''
  have hyQ : AffineMap.lineMap Q F s ≠ Q := by
    intro h
    have : AffineMap.lineMap Q F s = (AffineMap.lineMap Q F (0 : ℝ) : Plane) := by
      rw [h, AffineMap.lineMap_apply_zero]
    exact hs.ne' (AffineMap.lineMap_injective ℝ (farEnd_ne D he).symm this)
  have hlev : ∀ x ∈ edgesAt D Q, (∃ t : ℝ, farEnd D Q x = AffineMap.lineMap Q F t) →
      x ∈ D.lineChain g c ∨ x ∈ D.lineChain (-g) (-c) := by
    rintro x hx ⟨t, ht⟩
    exact edgesAt_chain D hx hgQ (by rw [ht]; exact level_lineMap hgQ hgF t)
  have c0 := hlev e he ⟨1, (AffineMap.lineMap_apply_one Q F).symm⟩
  have c1 := hlev e' he' ⟨t', hF'⟩
  have c2 := hlev e'' he'' ⟨t'', hF''⟩
  have key : ∀ {g' : Plane →ₗ[ℝ] ℝ} {c' : ℝ}, g' ≠ 0 → ∀ x y : Fin N × Fin 3,
      (Q ∈ (D.tile x.1).edge x.2 ∧ AffineMap.lineMap Q F s ∈ (D.tile x.1).edge x.2) →
      (Q ∈ (D.tile y.1).edge y.2 ∧ AffineMap.lineMap Q F s ∈ (D.tile y.1).edge y.2) →
      x ≠ y → x ∈ D.lineChain g' c' → y ∈ D.lineChain g' c' → False := by
    intro g' c' hg' x y hx hy' hxy hxc hyc
    exact hxy (lineChain_eq_of_two D hg' hxc hyc hyQ.symm ⟨hx.1, hy'.1⟩ ⟨hx.2, hy'.2⟩)
  have hng : -g ≠ 0 := neg_ne_zero.mpr hg
  rcases c0 with c0 | c0 <;> rcases c1 with c1 | c1 <;> rcases c2 with c2 | c2
  · exact key hg e e' y0 y1 h1.symm c0 c1
  · exact key hg e e' y0 y1 h1.symm c0 c1
  · exact key hg e e'' y0 y2 h2.symm c0 c2
  · exact key hng e' e'' y1 y2 h3 c1 c2
  · exact key hg e' e'' y1 y2 h3 c1 c2
  · exact key hng e e'' y0 y2 h2.symm c0 c2
  · exact key hng e e' y0 y1 h1.symm c0 c1
  · exact key hng e e' y0 y1 h1.symm c0 c1

/-- **An edge alone on its ray.** Let `e` be an edge at `Q`, in the chain of its line on the side
`g ≤ c`, with no other edge at `Q` along its ray. If some point strictly inside `e` is interior to
the target, then `Q` lies strictly inside an edge of the other chain. -/
theorem lonely_openSegment {Q : Plane} {e : Fin N × Fin 3} (he : e ∈ edgesAt D Q)
    {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) (hgQ : g Q = c) (hgF : g (farEnd D Q e) = c)
    (hec : e ∈ D.lineChain g c)
    (hlonely : ∀ e' ∈ edgesAt D Q, e' ≠ e → ¬ SameRayAt D Q e e')
    {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    (hint : AffineMap.lineMap Q (farEnd D Q e) τ ∈ interior D.target.carrier) :
    ∃ e₂ ∈ D.lineChain (-g) (-c),
      Q ∈ openSegment ℝ ((D.tile e₂.1).pts e₂.2) ((D.tile e₂.1).pts (e₂.2 + 1)) := by
  set F := farEnd D Q e
  have hQF : Q ≠ F := (farEnd_ne D he).symm
  have hng : -g ≠ 0 := neg_ne_zero.mpr hg
  have hnQ : (-g) Q = -c := by simp [hgQ]
  have hnF : (-g) F = -c := by simp [hgF]
  have hL0 : AffineMap.lineMap Q F (0 : ℝ) = Q := AffineMap.lineMap_apply_zero Q F
  -- `Q` is in the target.
  have hQt : Q ∈ D.target.carrier := by
    rw [← D.covers]
    refine Set.mem_iUnion.mpr ⟨e.1, ?_⟩
    have : Q ∈ (D.tile e.1).edge e.2 := by rw [edgesAt_edge D he]; exact left_mem_segment ℝ _ _
    exact (D.tile e.1).edge_subset_carrier e.2 this
  -- The open segment from `Q` to the interior point is interior and a wall.
  have hseg : openSegment ℝ (AffineMap.lineMap Q F (0 : ℝ)) (AffineMap.lineMap Q F τ)
      ⊆ interior D.target.carrier := by
    rw [hL0]
    exact D.target.convex.openSegment_closure_interior_subset_interior (subset_closure hQt) hint
  have hwall : ∀ y ∈ openSegment ℝ (AffineMap.lineMap Q F (0 : ℝ)) (AffineMap.lineMap Q F τ),
      ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    rw [← image_openSegment, openSegment_eq_Ioo hτ.1] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    exact D.edge_point_not_interior (mem_edge_of_ray D he (t := 1)
      (AffineMap.lineMap_apply_one Q F).symm hs.1.le (hs.2.le.trans hτ.2.le))
  -- The other chain reaches `Q` from the ray.
  obtain ⟨e₂, he₂, hlo, hhi⟩ := exists_interval_right (D.lineChain (-g) (-c))
    (fun x => edgeLo Q F (D.tile x.1) x.2) (fun x => edgeHi Q F (D.tile x.1) x.2) 0
    hτ.1 (vertex_params_finite D hQF) (fun y hy hyv => by
      rw [zero_add] at hy
      exact wall_cover_param D hng hQF hnQ hnF hτ.1 hseg hwall hy hyv)
  obtain ⟨n1, n2⟩ := lineChain_ends D he₂
  have n1' : g ((D.tile e₂.1).pts e₂.2) = c := by simpa using n1
  have n2' : g ((D.tile e₂.1).pts (e₂.2 + 1)) = c := by simpa using n2
  rcases hlo.lt_or_eq with hlo | hlo
  · refine ⟨e₂, he₂, ?_⟩
    rw [← hL0]
    exact (lineMap_mem_openSegment_iff hg hQF hgQ hgF _ _ n1' n2' 0).mpr ⟨hlo, hhi⟩
  · exfalso
    -- `Q` is an end of `e₂`, which then shares the ray of `e`.
    have hne : e₂ ≠ e := fun h => not_mem_both_chains D hg hec (h ▸ he₂)
    have e1 := eq_lineMap_lineParam hg hQF hgQ hgF n1'
    have e2 := eq_lineMap_lineParam hg hQF hgQ hgF n2'
    simp only [edgeLo, edgeHi] at hlo hhi
    rcases min_choice (lineParam Q F ((D.tile e₂.1).pts e₂.2))
      (lineParam Q F ((D.tile e₂.1).pts (e₂.2 + 1))) with hm | hm
    · rw [hm] at hlo
      have hQ2 : (D.tile e₂.1).pts e₂.2 = Q := by rw [← e1, hlo, hL0]
      have hmem : e₂ ∈ edgesAt D Q := (mem_edgesAt D).mpr (Or.inl hQ2)
      refine hlonely e₂ hmem hne ⟨lineParam Q F ((D.tile e₂.1).pts (e₂.2 + 1)), ?_, ?_⟩
      · rcases max_choice (lineParam Q F ((D.tile e₂.1).pts e₂.2))
          (lineParam Q F ((D.tile e₂.1).pts (e₂.2 + 1))) with h' | h'
        · rw [h', hlo] at hhi; exact absurd hhi (lt_irrefl _)
        · rw [h'] at hhi; exact hhi
      · rw [farEnd, if_pos hQ2, e2]
    · rw [hm] at hlo
      have hQ2 : (D.tile e₂.1).pts (e₂.2 + 1) = Q := by rw [← e2, hlo, hL0]
      have hmem : e₂ ∈ edgesAt D Q := (mem_edgesAt D).mpr (Or.inr hQ2)
      have hQ1 : (D.tile e₂.1).pts e₂.2 ≠ Q := fun h0 =>
        tri_pts_succ_ne (D.tile e₂.1) e₂.2 (h0.trans hQ2.symm)
      refine hlonely e₂ hmem hne ⟨lineParam Q F ((D.tile e₂.1).pts e₂.2), ?_, ?_⟩
      · rcases max_choice (lineParam Q F ((D.tile e₂.1).pts e₂.2))
          (lineParam Q F ((D.tile e₂.1).pts (e₂.2 + 1))) with h' | h'
        · rw [h'] at hhi; exact hhi
        · rw [h', hlo] at hhi; exact absurd hhi (lt_irrefl _)
      · rw [farEnd, if_neg hQ1, e1]

end EdgesAt

end TriangleTiling
