/-
Relations between the lengths of tile edges.

A relation between edges (marked edges of one type on one side, edges including one of another
type on the other, with equal total lengths) gives an integer relation between the sides
`a, b, c` of the tile: `J c = p a + q b`, or `J a = p b + q c`, with `J > 0`.
-/
import TriangleTiling.Tiling.Degree
import TriangleTiling.Isosceles.MarkedCount

namespace TriangleTiling

open Erdos634.Geometry

variable {N : ℕ} (D : CongruentDissection N)

/-- The sides of the tile are positive. -/
theorem model_sides_pos :
    0 < dist (D.model.pts 1) (D.model.pts 2) ∧ 0 < dist (D.model.pts 2) (D.model.pts 0) ∧
      0 < dist (D.model.pts 0) (D.model.pts 1) := by
  have hne : ∀ i j : Fin 3, i ≠ j → D.model.pts i ≠ D.model.pts j :=
    fun i j h e => h (D.model.indep.injective e)
  exact ⟨dist_pos.mpr (hne 1 2 (by decide)), dist_pos.mpr (hne 2 0 (by decide)),
    dist_pos.mpr (hne 0 1 (by decide))⟩

variable (hsep : AnglesSep D)
include hsep

open Classical in
/-- **A relation between edges, in the tile's sides.** If marked edges of type `φ` and edges
including one of another type have equal total lengths, then the sides `a, b, c` (opposite `α`,
`β`, `γ`) satisfy `n₁ · (side φ) = pα a + pβ b + pγ c`, where all of `s₁` is of type `φ`. -/
theorem relation_counts {φ : ℝ} (h : HasRelation D.toDissection (edgeType D φ)) :
    ∃ (s₁ s₂ : Finset (Fin N × Fin 3)), (∀ e ∈ s₁, edgeType D φ e) ∧
      (∃ e ∈ s₂, ¬ edgeType D φ e) ∧
      ((s₁.filter (edgeType D (tileα D))).card : ℝ) * dist (D.model.pts 1) (D.model.pts 2)
        + ((s₁.filter (edgeType D (tileβ D))).card : ℝ) * dist (D.model.pts 2) (D.model.pts 0)
        + ((s₁.filter (edgeType D (tileγ D))).card : ℝ) * dist (D.model.pts 0) (D.model.pts 1)
      = ((s₂.filter (edgeType D (tileα D))).card : ℝ) * dist (D.model.pts 1) (D.model.pts 2)
        + ((s₂.filter (edgeType D (tileβ D))).card : ℝ) * dist (D.model.pts 2) (D.model.pts 0)
        + ((s₂.filter (edgeType D (tileγ D))).card : ℝ) * dist (D.model.pts 0) (D.model.pts 1) := by
  obtain ⟨s₁, s₂, h1, h2, hsum⟩ := h
  refine ⟨s₁, s₂, h1, h2, ?_⟩
  have w1 := side_walk_counts_sep D hsep s₁ _ rfl
  have w2 := side_walk_counts_sep D hsep s₂ _ rfl
  unfold edgeType
  rw [← w1, ← w2]
  exact hsum

/-- The three edge types are different. -/
theorem types_ne : tileα D ≠ tileβ D ∧ tileα D ≠ tileγ D ∧ tileβ D ≠ tileγ D := by
  have hinj := hsep.2
  have ne : ∀ x y : Fin 5, x ≠ y →
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hinj.ne h
  exact ⟨ne 0 1 (by decide), ne 0 2 (by decide), ne 1 2 (by decide)⟩

open Classical in
/-- **A relation for `c` from edges**: `J c = p a + q b` with `J > 0`. -/
theorem c_relation_of_edges (h : HasRelation D.toDissection (edgeType D (tileγ D))) :
    ∃ J p q : ℕ, 0 < J ∧
    (J : ℝ) * dist (D.model.pts 0) (D.model.pts 1)
      = p * dist (D.model.pts 1) (D.model.pts 2) + q * dist (D.model.pts 2) (D.model.pts 0) := by
  obtain ⟨hαβ, hαγ, hβγ⟩ := types_ne D hsep
  obtain ⟨ha, hb, hc⟩ := model_sides_pos D
  obtain ⟨s₁, s₂, h1, ⟨e, he, hne⟩, hrel⟩ :=
    relation_counts D hsep h
  have f1 : s₁.filter (edgeType D (tileα D)) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun x hx h' => hαγ (h'.symm.trans (h1 x hx))
  have f2 : s₁.filter (edgeType D (tileβ D)) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun x hx h' => hβγ (h'.symm.trans (h1 x hx))
  have f3 : s₁.filter (edgeType D (tileγ D)) = s₁ := Finset.filter_true_of_mem h1
  rw [f1, f2, f3, Finset.card_empty, Nat.cast_zero, zero_mul, zero_mul, zero_add, zero_add] at hrel
  set pα := (s₂.filter (edgeType D (tileα D))).card
  set pβ := (s₂.filter (edgeType D (tileβ D))).card
  set pγ := (s₂.filter (edgeType D (tileγ D))).card
  -- The unmarked edge is an `a` or a `b` edge.
  have hpos : 1 ≤ pα + pβ := by
    rcases localAngle_at_own_vertex_mem' D e.1 (e.2 + 2) with h | h | h
    · have : 1 ≤ pα := Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, h⟩⟩; omega
    · have : 1 ≤ pβ := Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, h⟩⟩; omega
    · exact absurd h hne
  have hlt : pγ < s₁.card := by
    by_contra hle
    push Not at hle
    have h3 : (s₁.card : ℝ) ≤ pγ := by exact_mod_cast hle
    have h4 : (1 : ℝ) ≤ pα + pβ := by exact_mod_cast hpos
    have h5 : (0 : ℝ) < pα * dist (D.model.pts 1) (D.model.pts 2)
        + pβ * dist (D.model.pts 2) (D.model.pts 0) := by
      rcases Nat.eq_zero_or_pos pα with h0 | h0
      · have : (1 : ℝ) ≤ pβ := by rw [h0] at hpos; exact_mod_cast (by omega : 1 ≤ pβ)
        rw [h0, Nat.cast_zero, zero_mul, zero_add]; nlinarith
      · have : (1 : ℝ) ≤ pα := by exact_mod_cast h0
        have : (0 : ℝ) ≤ pβ := Nat.cast_nonneg _
        nlinarith
    nlinarith
  refine ⟨s₁.card - pγ, pα, pβ, by omega, ?_⟩
  rw [Nat.cast_sub hlt.le]
  linarith

open Classical in
/-- **A relation for `a` from edges**: `J a = p b + q c` with `J > 0`. -/
theorem a_relation_of_edges (h : HasRelation D.toDissection (edgeType D (tileα D))) :
    ∃ J p q : ℕ, 0 < J ∧
    (J : ℝ) * dist (D.model.pts 1) (D.model.pts 2)
      = p * dist (D.model.pts 2) (D.model.pts 0) + q * dist (D.model.pts 0) (D.model.pts 1) := by
  obtain ⟨hαβ, hαγ, hβγ⟩ := types_ne D hsep
  obtain ⟨ha, hb, hc⟩ := model_sides_pos D
  obtain ⟨s₁, s₂, h1, ⟨e, he, hne⟩, hrel⟩ :=
    relation_counts D hsep h
  have f1 : s₁.filter (edgeType D (tileα D)) = s₁ := Finset.filter_true_of_mem h1
  have f2 : s₁.filter (edgeType D (tileβ D)) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun x hx h' => hαβ ((h1 x hx).symm.trans h')
  have f3 : s₁.filter (edgeType D (tileγ D)) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun x hx h' => hαγ ((h1 x hx).symm.trans h')
  rw [f1, f2, f3, Finset.card_empty, Nat.cast_zero, zero_mul, zero_mul, add_zero, add_zero] at hrel
  set pα := (s₂.filter (edgeType D (tileα D))).card
  set pβ := (s₂.filter (edgeType D (tileβ D))).card
  set pγ := (s₂.filter (edgeType D (tileγ D))).card
  have hpos : 1 ≤ pβ + pγ := by
    rcases localAngle_at_own_vertex_mem' D e.1 (e.2 + 2) with h | h | h
    · exact absurd h hne
    · have : 1 ≤ pβ := Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, h⟩⟩; omega
    · have : 1 ≤ pγ := Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, h⟩⟩; omega
  have hlt : pα < s₁.card := by
    by_contra hle
    push Not at hle
    have h3 : (s₁.card : ℝ) ≤ pα := by exact_mod_cast hle
    have h5 : (0 : ℝ) < pβ * dist (D.model.pts 2) (D.model.pts 0)
        + pγ * dist (D.model.pts 0) (D.model.pts 1) := by
      rcases Nat.eq_zero_or_pos pβ with h0 | h0
      · have : (1 : ℝ) ≤ pγ := by rw [h0] at hpos; exact_mod_cast (by omega : 1 ≤ pγ)
        rw [h0, Nat.cast_zero, zero_mul, zero_add]; nlinarith
      · have : (1 : ℝ) ≤ pβ := by exact_mod_cast h0
        have : (0 : ℝ) ≤ pγ := Nat.cast_nonneg _
        nlinarith
    nlinarith
  refine ⟨s₁.card - pα, pβ, pγ, by omega, ?_⟩
  rw [Nat.cast_sub hlt.le]
  linarith


end TriangleTiling
