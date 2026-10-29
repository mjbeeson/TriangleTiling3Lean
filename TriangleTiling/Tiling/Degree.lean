/-
From an arriving link to a leaving one (the paper's `lemma:propagation` and the step of
`lemma:crelation4` that follows a link).

At a vertex `V`, call a marked edge *lonely* if no other edge at `V` shares its ray. If the marked
edges at `V` are even in number while exactly one of them is lonely, some ray carries a marked edge
together with an unmarked one (the parity count of `EdgesAt`). Extending that ray gives a link
from `V`, or a relation between edge lengths.

At the end of a link the lonely marked edge is the arriving one, so a link leaves the end of
every link at which the marked edges are even in number, unless there is a relation.
-/
import TriangleTiling.Tiling.LinkEnd

namespace TriangleTiling

open Erdos634.Geometry Set

variable {N : ℕ} (D : Dissection N) (isθ : Fin N × Fin 3 → Prop)

/-- A relation between edge lengths: marked edges on one side, edges including an unmarked one on
the other, with equal total lengths. -/
def HasRelation : Prop :=
  ∃ s₁ s₂ : Finset (Fin N × Fin 3), (∀ e ∈ s₁, isθ e) ∧ (∃ e ∈ s₂, ¬ isθ e) ∧
    ∑ e ∈ s₁, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
      = ∑ e ∈ s₂, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))

/-- Edges at `V` sharing a ray. -/
def Partners (V : Plane) (x y : Fin N × Fin 3) : Prop := x ≠ y ∧ SameRayAt D V x y

open Classical in
/-- **A mixed ray from parity.** If the marked edges at `V` are even in number and exactly one of
them, `e₀`, is lonely, some ray at `V` carries a marked and an unmarked edge. -/
theorem mixed_of_parity {V : Plane} {e₀ : Fin N × Fin 3} (he₀ : e₀ ∈ edgesAt D V)
    (hθ₀ : isθ e₀) (hl₀ : ∀ e' ∈ edgesAt D V, ¬ Partners D V e₀ e')
    (huniq : ∀ e ∈ edgesAt D V, isθ e → (∀ e' ∈ edgesAt D V, ¬ Partners D V e e') → e = e₀)
    (heven : Even ((edgesAt D V).filter isθ).card) :
    ∃ x ∈ edgesAt D V, ∃ y ∈ edgesAt D V, Partners D V x y ∧ isθ x ∧ ¬ isθ y := by
  by_contra hno
  push Not at hno
  have hpar := card_filter_mod_two (edgesAt D V) (Partners D V) isθ
    (fun x _ y _ h => ⟨h.1.symm, sameRayAt_symm D h.2⟩) (fun x h => h.1 rfl)
    (fun x hx y hy z hz hxy hxz => by
      by_contra hyz
      exact sameRayAt_unique D hx hy hz hxy.1.symm hxz.1.symm hyz hxy.2 hxz.2)
    (fun x hx y hy hxy hθ => by
      exact hno x hx y hy hxy hθ) {e₀} (fun x => by
        rw [Finset.mem_singleton]
        constructor
        · rintro rfl
          exact ⟨he₀, hθ₀, hl₀⟩
        · rintro ⟨hx, hθ, hl⟩
          exact huniq x hx hθ hl)
  rw [Finset.card_singleton, Nat.even_iff.mp heven] at hpar
  exact absurd hpar (by norm_num)

open Classical in
/-- **A link leaves the end of a link**, if the marked edges there are even in number and there is
no relation. -/
theorem out_of_in {Q R : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (h : LinkData D isθ Q R g c)
    (heven : Even ((edgesAt D R).filter isθ).card) (hnorel : ¬ HasRelation D isθ) :
    ∃ R', IsLink D isθ R R' := by
  obtain ⟨e₀, he₀, hθ₀, hl₀, huniq⟩ := h.lonely_marked
  obtain ⟨x, hx, y, hy, hxy, hθx, hθy⟩ := mixed_of_parity D isθ he₀ hθ₀
    (fun e' he' h' => hl₀ e' he' h') (fun e he hθ hl => huniq e he hθ (fun e' he' h' => hl e' he' h'))
    heven
  rcases extend_link D isθ hx hy hxy.1.symm hxy.2 hθx hθy
    (h.back_of_partner hx hy hxy.1 hxy.2) with hlink | hrel
  · exact hlink
  · exact absurd hrel hnorel

open Classical in
/-- **Links have one tail and one head**: out-degrees and in-degrees have the same total. -/
theorem sum_out_eq_sum_in (V : Finset Plane) :
    ∑ v ∈ V, (V.filter fun w => IsLink D isθ v w).card
      = ∑ w ∈ V, (V.filter fun v => IsLink D isθ v w).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

open Classical in
/-- In-degrees are at most one. -/
theorem in_le_one (V : Finset Plane) (w : Plane) :
    (V.filter fun v => IsLink D isθ v w).card ≤ 1 :=
  Finset.card_le_one.mpr fun _ ha _ hb =>
    link_unique D isθ (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2

open Classical in
/-- The vertices of the tiling. -/
noncomputable def vertexFinset : Finset Plane :=
  Finset.univ.image fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2

/-- The ends of links are vertices. -/
theorem link_mem_vertexFinset {u w : Plane} (h : IsLink D isθ u w) :
    u ∈ vertexFinset D ∧ w ∈ vertexFinset D := by
  classical
  obtain ⟨g, c, h⟩ := h
  obtain ⟨i, k, hik⟩ := h.start_vertex
  obtain ⟨i', k', hik'⟩ := h.end_vertex
  exact ⟨Finset.mem_image.mpr ⟨(i, k), Finset.mem_univ _, hik⟩,
    Finset.mem_image.mpr ⟨(i', k'), Finset.mem_univ _, hik'⟩⟩

open Classical in
/-- **A link from the boundary forces a relation.** If at the end of every link the marked edges
are even in number, and a link starts at a boundary point, then there is a relation: else every
link would be followed by another, and the link from the boundary, where no link ends, would make
links outnumber themselves. -/
theorem relation_of_start
    (heven : ∀ Q R g c, LinkData D isθ Q R g c → Even ((edgesAt D R).filter isθ).card)
    (hstart : ∃ Q₀ ∈ frontier D.target.carrier, ∃ R, IsLink D isθ Q₀ R) :
    HasRelation D isθ := by
  by_contra hnorel
  obtain ⟨Q₀, hQ₀fr, R₀, hlink₀⟩ := hstart
  set V := vertexFinset D
  have hge : ∀ v ∈ V, (V.filter fun u => IsLink D isθ u v).card ≤
      (V.filter fun w => IsLink D isθ v w).card := by
    intro v _
    rcases Nat.eq_zero_or_pos (V.filter fun u => IsLink D isθ u v).card with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
      obtain ⟨-, g, c, hl⟩ := Finset.mem_filter.mp hu
      obtain ⟨R', hR'⟩ := out_of_in D isθ hl (heven _ _ _ _ hl) hnorel
      have : 1 ≤ (V.filter fun w => IsLink D isθ v w).card :=
        Finset.card_pos.mpr ⟨R', Finset.mem_filter.mpr ⟨(link_mem_vertexFinset D isθ hR').2, hR'⟩⟩
      linarith [in_le_one D isθ V v]
  have hin0 : (V.filter fun u => IsLink D isθ u Q₀).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro u - ⟨g, c, hl⟩
    exact hQ₀fr.2 hl.end_interior
  have hout : 0 < (V.filter fun w => IsLink D isθ Q₀ w).card :=
    Finset.card_pos.mpr ⟨R₀, Finset.mem_filter.mpr ⟨(link_mem_vertexFinset D isθ hlink₀).2,
      hlink₀⟩⟩
  have hlt := Finset.sum_lt_sum hge
    ⟨Q₀, (link_mem_vertexFinset D isθ hlink₀).1, by rw [hin0]; exact hout⟩
  rw [sum_out_eq_sum_in] at hlt
  exact lt_irrefl _ hlt

end TriangleTiling
