/-
How many edges of each type end at a vertex.

An edge has type `φ` when the tile's angle opposite it is `φ` (the `a`, `b`, `c` edges are those
of type `α`, `β`, `γ`). A tile with a vertex at `Q` has two edges ending at `Q`, opposite its two
angles away from `Q`; so the edges of type `φ` ending at `Q` are as many as the tiles at `Q`
whose angle there is not `φ`.
-/
import TriangleTiling.Tiling.EdgesAt
import TriangleTiling.Isosceles.NotSquarefree

namespace TriangleTiling

open Erdos634.Geometry

variable {N : ℕ} (D : CongruentDissection N)

/-- The edge `e` has type `φ`: the angle of its tile opposite it is `φ`. -/
def edgeType (φ : ℝ) (e : Fin N × Fin 3) : Prop :=
  (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = φ

/-- A sum over the two edges of a triangle at its vertex `k0`. -/
theorem sum_two_edges (k0 : Fin 3) (f : Fin 3 → Prop) [DecidablePred f] :
    (∑ k : Fin 3, if (k = k0 ∨ k = k0 + 2) ∧ f k then (1 : ℕ) else 0)
      = (if f k0 then 1 else 0) + (if f (k0 + 2) then 1 else 0) := by
  rw [Fin.sum_univ_three]
  fin_cases k0 <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceAdd,
    Fin.reduceEq, or_true, or_false, true_and, false_and, if_false, add_zero, zero_add,
    or_self] <;> split_ifs <;> simp

/-- A count over the three vertices of a triangle, starting anywhere. -/
theorem card_three (k0 : Fin 3) (p : Fin 3 → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card
      = (if p k0 then 1 else 0) + (if p (k0 + 1) then 1 else 0) + (if p (k0 + 2) then 1 else 0) := by
  rw [Finset.card_filter, Fin.sum_univ_three]
  fin_cases k0 <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
    Fin.reduceAdd] <;> split_ifs <;> simp

variable (hsep : AnglesSep D)
include hsep

/-- Away from its vertices, a tile's local angle is none of `α, β, γ`. -/
theorem localAngle_ne_of_not_vertex {i : Fin N} {Q : Plane} (hQ : ∀ k, (D.tile i).pts k ≠ Q)
    {φ : ℝ} (hφ : φ = tileα D ∨ φ = tileβ D ∨ φ = tileγ D) : (D.tile i).localAngle Q ≠ φ := by
  have ⟨hv0, hinj⟩ := hsep
  have ne : ∀ x y : Fin 5, x ≠ y →
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hinj.ne h
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) Q with ⟨j, hj, -⟩ | h | h | h
  · exact absurd hj.symm (hQ j)
  · rw [h]
    rcases hφ with rfl | rfl | rfl
    · exact (ne 4 0 (by decide))
    · exact (ne 4 1 (by decide))
    · exact (ne 4 2 (by decide))
  · rw [h]
    rcases hφ with rfl | rfl | rfl
    · exact (ne 3 0 (by decide))
    · exact (ne 3 1 (by decide))
    · exact (ne 3 2 (by decide))
  · rw [h]
    rcases hφ with rfl | rfl | rfl
    · exact (hv0 0).symm
    · exact (hv0 1).symm
    · exact (hv0 2).symm

open Classical in
/-- **Edges of type `φ` at `Q`, per tile.** -/
theorem tile_marked_count (i : Fin N) (Q : Plane) {φ : ℝ}
    (hφ : φ = tileα D ∨ φ = tileβ D ∨ φ = tileγ D) :
    (∑ k : Fin 3, if ((D.tile i).pts k = Q ∨ (D.tile i).pts (k + 1) = Q) ∧
        edgeType D φ (i, k) then 1 else 0)
      + (if (D.tile i).localAngle Q = φ then 1 else 0)
      = (if (D.tile i).localAngle Q = tileα D then 1 else 0)
        + (if (D.tile i).localAngle Q = tileβ D then 1 else 0)
        + (if (D.tile i).localAngle Q = tileγ D then 1 else 0) := by
  have ⟨hv0, hinj⟩ := hsep
  have ne : ∀ x y : Fin 5, x ≠ y →
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hinj.ne h
  have hαβ : tileα D ≠ tileβ D := ne 0 1 (by decide)
  have hαγ : tileα D ≠ tileγ D := ne 0 2 (by decide)
  have hβγ : tileβ D ≠ tileγ D := ne 1 2 (by decide)
  by_cases hv : ∃ k0, (D.tile i).pts k0 = Q
  · obtain ⟨k0, hk0⟩ := hv
    have hinj' := (D.tile i).indep.injective
    -- The edges at `Q` are `k0` and `k0 + 2`.
    have hcond : ∀ k : Fin 3, ((D.tile i).pts k = Q ∨ (D.tile i).pts (k + 1) = Q) ↔
        (k = k0 ∨ k = k0 + 2) := by
      intro k
      rw [← hk0]
      constructor
      · rintro (h | h)
        · exact Or.inl (hinj' h)
        · right
          have := hinj' h
          rw [← this]
          fin_cases k <;> rfl
      · rintro (rfl | rfl)
        · exact Or.inl rfl
        · right
          congr 1
          fin_cases k0 <;> rfl
    simp only [hcond]
    rw [sum_two_edges k0 (fun k => edgeType D φ (i, k))]
    -- The angles at the three corners are `α, β, γ` in some order.
    have hloc : ∀ k, (D.tile i).localAngle ((D.tile i).pts k)
        = cornerAngle ((D.tile i).pts (k + 1)) ((D.tile i).pts k) ((D.tile i).pts (k + 2)) :=
      Tri.localAngle_vertex _
    obtain ⟨cα, cβ, cγ⟩ := tile_angle_count_sep D hsep i
    have hone : (if (D.tile i).localAngle ((D.tile i).pts k0) = φ then 1 else 0)
        + (if (D.tile i).localAngle ((D.tile i).pts (k0 + 1)) = φ then 1 else 0)
        + (if (D.tile i).localAngle ((D.tile i).pts (k0 + 2)) = φ then 1 else 0) = 1 := by
      have hc : (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
          ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = φ).card = 1 := by
        rcases hφ with rfl | rfl | rfl
        · exact cα
        · exact cβ
        · exact cγ
      simp only [← hloc] at hc
      have h3 := card_three k0 (fun k => (D.tile i).localAngle ((D.tile i).pts k) = φ)
      rw [hc] at h3
      exact h3.symm
    have hk2 : k0 + 2 + 2 = k0 + 1 := by fin_cases k0 <;> rfl
    have e1 : edgeType D φ (i, k0) ↔ (D.tile i).localAngle ((D.tile i).pts (k0 + 2)) = φ :=
      Iff.rfl
    have e2 : edgeType D φ (i, k0 + 2) ↔ (D.tile i).localAngle ((D.tile i).pts (k0 + 1)) = φ := by
      show (D.tile i).localAngle ((D.tile i).pts (k0 + 2 + 2)) = φ ↔ _
      rw [hk2]
    simp only [e1, e2]
    rw [← hk0]
    set θ := (D.tile i).localAngle ((D.tile i).pts k0)
    rcases localAngle_at_own_vertex_mem' D i k0 with h | h | h
    · have n1 : ¬ θ = tileβ D := fun h' => hαβ (h.symm.trans h')
      have n2 : ¬ θ = tileγ D := fun h' => hαγ (h.symm.trans h')
      rw [if_pos h, if_neg n1, if_neg n2]
      omega
    · have n1 : ¬ θ = tileα D := fun h' => hαβ (h'.symm.trans h)
      have n2 : ¬ θ = tileγ D := fun h' => hβγ (h.symm.trans h')
      rw [if_neg n1, if_pos h, if_neg n2]
      omega
    · have n1 : ¬ θ = tileα D := fun h' => hαγ (h'.symm.trans h)
      have n2 : ¬ θ = tileβ D := fun h' => hβγ (h'.symm.trans h)
      rw [if_neg n1, if_neg n2, if_pos h]
      omega
  · push Not at hv
    have h0 : ∀ k : Fin 3, ¬ (((D.tile i).pts k = Q ∨ (D.tile i).pts (k + 1) = Q) ∧
        edgeType D φ (i, k)) := fun k h => by
      rcases h.1 with h' | h'
      · exact hv k h'
      · exact hv (k + 1) h'
    simp only [h0, if_false, Finset.sum_const_zero, zero_add]
    rw [if_neg (localAngle_ne_of_not_vertex D hsep hv hφ),
      if_neg (localAngle_ne_of_not_vertex D hsep hv (Or.inl rfl)),
      if_neg (localAngle_ne_of_not_vertex D hsep hv (Or.inr (Or.inl rfl))),
      if_neg (localAngle_ne_of_not_vertex D hsep hv (Or.inr (Or.inr rfl)))]

open Classical in
/-- **Edges of type `φ` at `Q`**: as many as the tiles at `Q` with angle `α, β, γ`, less those with
angle `φ`. -/
theorem card_marked (Q : Plane) {φ : ℝ} (hφ : φ = tileα D ∨ φ = tileβ D ∨ φ = tileγ D) :
    ((edgesAt D.toDissection Q).filter (edgeType D φ)).card + angleCount D Q φ
      = angleCount D Q (tileα D) + angleCount D Q (tileβ D) + angleCount D Q (tileγ D) := by
  have hfilt : (edgesAt D.toDissection Q).filter (edgeType D φ) = Finset.univ.filter fun e =>
      ((D.tile e.1).pts e.2 = Q ∨ (D.tile e.1).pts (e.2 + 1) = Q) ∧ edgeType D φ e := by
    rw [edgesAt, Finset.filter_filter]
  rw [hfilt, Finset.card_filter, Fintype.sum_prod_type]
  simp only [angleCount, Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => tile_marked_count D hsep i Q hφ

end TriangleTiling
