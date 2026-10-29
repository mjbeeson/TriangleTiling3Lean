/-
`lemma:twocs` of M. Beeson, *Triangle tiling: the case 3α + 2β = π* (arXiv 1206.2229v4): at least
two `c` edges on the side `AC`.

**Statement not yet checked by Beeson.** It adds the hypothesis that `AC` is not a single `c` edge
(`|AC| ≠ c`), agreed with Beeson on 2026-10-24: the printed proof does not cover Case 1c with
`P = A`, `Q = C` (see `TriangleTiling3-suggested-changes.md`, item 23).

The proof (`TwoCs.twocs_core`) relabels the model so that its angles at `model.pts 0, 1, 2` are
`α, β, γ` with `α < β`, and the target so that `AC` is the side from `target.pts 0` to
`target.pts 1`.
-/
import TriangleTiling.TwoCs.Core
import TriangleTiling.ThreeAlpha.ARelation

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry EuclideanGeometry Set TriangleTiling.TwoCs

variable {N : ℕ} (D : CongruentDissection N)

/-- After relabelling the model by the permutation of `TileSides`, `tileα`, `tileβ`, `tileγ` are
`α`, `β`, `γ`, and the sides opposite them are `a`, `b`, `c`. -/
theorem relabel_sides {α β γ a b c : ℝ} (h : TileSides D α β γ a b c) :
    ∃ τ : Equiv.Perm (Fin 3), tileα (relabelModel D τ) = α ∧ tileβ (relabelModel D τ) = β ∧
      tileγ (relabelModel D τ) = γ ∧
      dist ((relabelModel D τ).model.pts 1) ((relabelModel D τ).model.pts 2) = a ∧
      dist ((relabelModel D τ).model.pts 2) ((relabelModel D τ).model.pts 0) = b ∧
      dist ((relabelModel D τ).model.pts 0) ((relabelModel D τ).model.pts 1) = c := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := h
  refine ⟨σ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [tileα, tileβ, tileγ, relabelModel, Function.comp]
    have d01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
    have d02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
    have d12 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  · rw [← h0]; unfold Tri.angleAt cornerAngle
    rcases others _ _ _ d01 d02 d12 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    exact EuclideanGeometry.angle_comm _ _ _
  · rw [← h1]; unfold Tri.angleAt cornerAngle
    rcases others _ _ _ d12 d01.symm d02.symm with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
      rw [e1, e2]
    exact EuclideanGeometry.angle_comm _ _ _
  · rw [← h2]; unfold Tri.angleAt cornerAngle
    rcases others _ _ _ d02.symm d12.symm d01 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    exact EuclideanGeometry.angle_comm _ _ _
  · rw [← l0]; unfold Tri.oppLen
    rcases others _ _ _ d01 d02 d12 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    exact dist_comm _ _
  · rw [← l1]; unfold Tri.oppLen
    rcases others _ _ _ d12 d01.symm d02.symm with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    exact dist_comm _ _
  · rw [← l2]; unfold Tri.oppLen
    rcases others _ _ _ d02.symm d12.symm d01 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    exact dist_comm _ _

/-- Swapping the names of `α` and `β`. -/
theorem tileSides_swap {α β γ a b c : ℝ} (h : TileSides D α β γ a b c) :
    TileSides D β α γ b a c := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := h
  refine ⟨(Equiv.swap 0 1).trans σ, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simpa

/-- The tile's angles are positive and add up to `π`. -/
theorem tileSides_angles {α β γ a b c : ℝ} (hT : TileSides D α β γ a b c) :
    0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = Real.pi := by
  obtain ⟨σ, h0, h1, h2, -, -, -⟩ := hT
  have hsum : D.model.angleAt (σ 0) + D.model.angleAt (σ 1) + D.model.angleAt (σ 2) = Real.pi := by
    have e := Equiv.sum_comp σ (fun k => D.model.angleAt k)
    simp only [Fin.sum_univ_three] at e
    rw [e, D.model.angleAt_sum]
  exact ⟨h0 ▸ D.model.angleAt_pos' _, h1 ▸ D.model.angleAt_pos' _, h2 ▸ D.model.angleAt_pos' _,
    by rw [← h0, ← h1, ← h2]; exact hsum⟩

open Classical in
/-- **Lemma `lemma:twocs`.** Suppose triangle `ABC` is `N`-tiled by a tile `T` with angles
`(α, β, γ)` (and sides `(a, b, c)` opposite them). Suppose (i) `γ > π/2`, (ii) `α/β` is not
rational, (iii) every angle of `ABC` is less than `γ`, and (iv) either neither of `a, b` is an
integer multiple of the other, or neither of the vertices `A, C` has two tiles with equal angles
there (two `α` angles or two `β` angles). Then there are at least two `c` edges of tiles on side
`AC`.

Added hypothesis (agreed with Beeson): `AC` is not a single `c` edge, `|AC| ≠ c`. -/
theorem twocs {α β γ a b c : ℝ} (hT : TileSides D α β γ a b c) (hγ : Real.pi / 2 < γ)
    (hirr : ¬ ∃ q : ℚ, α / β = q) (hlt : ∀ k, D.target.angleAt k < γ)
    (hiv : ((¬ ∃ n : ℕ, a = n * b) ∧ (¬ ∃ n : ℕ, b = n * a)) ∨
      (anglesAt D 0 α ≤ 1 ∧ anglesAt D 0 β ≤ 1 ∧ anglesAt D 2 α ≤ 1 ∧ anglesAt D 2 β ≤ 1))
    (hAC : dist (D.target.pts 0) (D.target.pts 2) ≠ c) :
    ∃ i j : Fin N, i ≠ j ∧
      (∃ m : Fin 3, (D.tile i).edge m ⊆ segment ℝ (D.target.pts 0) (D.target.pts 2) ∧
        dist ((D.tile i).pts m) ((D.tile i).pts (m + 1)) = c) ∧
      (∃ m : Fin 3, (D.tile j).edge m ⊆ segment ℝ (D.target.pts 0) (D.target.pts 2) ∧
        dist ((D.tile j).pts m) ((D.tile j).pts (m + 1)) = c) := by
  obtain ⟨hα, hβ, hγ0, hsum⟩ := tileSides_angles D hT
  have hαβne : α ≠ β := by
    intro h; apply hirr; exact ⟨1, by rw [h, div_self hβ.ne']; norm_num⟩
  wlog hαβ : α < β generalizing α β a b
  · have hba : β < α := lt_of_le_of_ne (not_lt.mp hαβ) hαβne.symm
    refine this (tileSides_swap D hT) ?_ ?_ hβ hα (by linarith) hαβne.symm hba
    · rintro ⟨q, hq⟩
      apply hirr
      refine ⟨q⁻¹, ?_⟩
      rw [Rat.cast_inv, ← hq, inv_div]
    · rcases hiv with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
      · exact Or.inl ⟨h2, h1⟩
      · exact Or.inr ⟨h2, h1, h4, h3⟩
  -- Normalize the model, and make `AC` the side `0 → 1`.
  obtain ⟨τ, eα, eβ, eγ, ea, eb, ec⟩ := relabel_sides D hT
  set D₁ := relabelModel D τ
  set D₂ := relabelTarget D₁ (Equiv.swap 1 2)
  have p0 : D₂.target.pts 0 = D.target.pts 0 := by
    show D.target.pts (Equiv.swap 1 2 0) = _
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
  have p1 : D₂.target.pts 1 = D.target.pts 2 := by
    show D.target.pts (Equiv.swap 1 2 1) = _
    rw [Equiv.swap_apply_left]
  have p2 : D₂.target.pts 2 = D.target.pts 1 := by
    show D.target.pts (Equiv.swap 1 2 2) = _
    rw [Equiv.swap_apply_right]
  have tα : tileα D₂ = α := eα
  have tβ : tileβ D₂ = β := eβ
  have tγ : tileγ D₂ = γ := eγ
  have hπ := Real.pi_pos
  have hsep : AnglesSep D₂ := by
    rw [AnglesSep, tα, tβ, tγ]
    refine ⟨fun j => ?_, fun i j h => ?_⟩
    · fin_cases j <;> simp <;> linarith
    · fin_cases i <;> fin_cases j <;> simp at h ⊢ <;>
        first | rfl | linarith
  have hγ₂ : Real.pi / 2 < tileγ D₂ := tγ ▸ hγ
  have hirr₂ : ¬ ∃ q : ℚ, tileα D₂ = (q : ℝ) * tileβ D₂ := by
    rintro ⟨q, hq⟩; apply hirr; refine ⟨q, ?_⟩; rw [tα, tβ] at hq; rw [hq]; field_simp
  have hαβ₂ : tileα D₂ < tileβ D₂ := by rw [tα, tβ]; exact hαβ
  have hcorner : ∀ k, D₂.target.localAngle (D₂.target.pts k) < tileγ D₂ := by
    intro k
    rw [tγ, Tri.localAngle_vertex, cornerAngle]
    have h0 := hlt 0; have h1 := hlt 1; have h2 := hlt 2
    unfold Tri.angleAt cornerAngle at h0 h1 h2
    fin_cases k
    · show ∠ (D₂.target.pts 1) (D₂.target.pts 0) (D₂.target.pts 2) < γ
      rw [p0, p1, p2, angle_comm]; exact h0
    · show ∠ (D₂.target.pts 2) (D₂.target.pts 1) (D₂.target.pts 0) < γ
      rw [p0, p1, p2, angle_comm]; exact h2
    · show ∠ (D₂.target.pts 0) (D₂.target.pts 2) (D₂.target.pts 1) < γ
      rw [p0, p1, p2, angle_comm]; exact h1
  -- Counts at the corners, by `anglesAt`.
  have hcnt : ∀ (k : Fin 3) {x : ℝ}, x ≠ 0 → x ≠ Real.pi → x ≠ 2 * Real.pi →
      angleCount D₂ (D.target.pts k) x = anglesAt D k x := by
    intro k x h0 hπ' h2π
    unfold angleCount anglesAt
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact localAngle_iff _ _ h0 hπ' h2π
  have hne5 := hsep.2
  rw [AnglesSep, tα, tβ, tγ] at hsep
  have hα0 : α ≠ 0 := hα.ne'
  have hβ0 : β ≠ 0 := hβ.ne'
  have hαπ : α ≠ Real.pi := by linarith
  have hβπ : β ≠ Real.pi := by linarith
  have hα2π : α ≠ 2 * Real.pi := by linarith
  have hβ2π : β ≠ 2 * Real.pi := by linarith
  have hsep₂ : AnglesSep D₂ := by rw [AnglesSep, tα, tβ, tγ]; exact hsep
  have hiv₂ : ((¬ ∃ n : ℕ, dist (D₂.model.pts 1) (D₂.model.pts 2) =
          n * dist (D₂.model.pts 2) (D₂.model.pts 0)) ∧
        (¬ ∃ n : ℕ, dist (D₂.model.pts 2) (D₂.model.pts 0) =
          n * dist (D₂.model.pts 1) (D₂.model.pts 2))) ∨
      (∀ V, (V = D₂.target.pts 0 ∨ V = D₂.target.pts 1) →
        angleCount D₂ V (tileα D₂) ≤ 1 ∧ angleCount D₂ V (tileβ D₂) ≤ 1) := by
    rcases hiv with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
    · left
      have ea' : dist (D₂.model.pts 1) (D₂.model.pts 2) = a := ea
      have eb' : dist (D₂.model.pts 2) (D₂.model.pts 0) = b := eb
      rw [ea', eb']; exact ⟨h1, h2⟩
    · right
      rintro V (rfl | rfl) <;> rw [tα, tβ]
      · rw [p0, hcnt 0 hα0 hαπ hα2π, hcnt 0 hβ0 hβπ hβ2π]; exact ⟨h1, h2⟩
      · rw [p1, hcnt 2 hα0 hαπ hα2π, hcnt 2 hβ0 hβπ hβ2π]; exact ⟨h3, h4⟩
  have hsingle : dist (D₂.target.pts 0) (D₂.target.pts 1) ≠
      dist (D₂.model.pts 0) (D₂.model.pts 1) := by
    rw [p0, p1]; exact fun h => hAC (h.trans ec)
  -- The side `AC`.
  obtain ⟨part, hcov, hdisj, -⟩ := D₂.toDissection.side_walk 0
  have hcov' : (⋃ e ∈ part, (D₂.tile e.1).edge e.2) =
      segment ℝ (D₂.target.pts 0) (D₂.target.pts (0 + 1)) := hcov
  set F := part.filter (fun e => (D₂.tile e.1).localAngle ((D₂.tile e.1).pts (e.2 + 2))
    = tileγ D₂)
  have hside : ∀ e ∈ part, (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 0) (D.target.pts 2) :=
    fun e he y hy => by
      have : y ∈ segment ℝ (D₂.target.pts 0) (D₂.target.pts (0 + 1)) := by
        rw [← hcov']; exact Set.mem_biUnion he hy
      rwa [show (0 : Fin 3) + 1 = 1 from rfl, p0, p1] at this
  have hlenc : ∀ e ∈ F, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = c := by
    intro e he
    have := TwoCs.edge_length D₂ hsep₂ e.1 e.2 2 (Finset.mem_filter.mp he).2
    rw [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl] at this
    exact this.trans ec
  by_cases h2 : 1 < F.card
  · obtain ⟨e₁, he₁, e₂, he₂, hne⟩ := Finset.one_lt_card.mp h2
    have hti : e₁.1 ≠ e₂.1 := by
      intro h
      apply hne
      have h1 := (Finset.mem_filter.mp he₁).2
      have h2' := (Finset.mem_filter.mp he₂).2
      rw [h] at h1
      have := TwoCs.corner_unique D₂ hsep₂ e₂.1 (Or.inr (Or.inr rfl)) h1 h2'
      have h3 : e₁.2 = e₂.2 := by
        revert this; generalize e₁.2 = x; generalize e₂.2 = y
        fin_cases x <;> fin_cases y <;> decide
      exact Prod.ext h h3
    exact ⟨e₁.1, e₂.1, hti, ⟨e₁.2, hside e₁ (Finset.mem_filter.mp he₁).1, hlenc e₁ he₁⟩,
      ⟨e₂.2, hside e₂ (Finset.mem_filter.mp he₂).1, hlenc e₂ he₂⟩⟩
  · exfalso
    push Not at h2
    -- One `c` edge at least (`lemma:pigeonhole`).
    have hz := fun k => (TwoCs.corner_counts D₂ hsep₂ hγ₂ k (hcorner k)).1
    obtain ⟨e₀, he₀, hγe⟩ := side_has_edge_sep D₂ hsep₂ (tileγ D₂) (Or.inr (Or.inr rfl)) 0 part
      hcov' hdisj (fun e _ _ => ne_of_angleCount_zero D₂ (hz 0) e.1)
      (fun e _ _ => ne_of_angleCount_zero D₂ (hz 1) e.1) (fun P hP => by
        by_cases hPc : P ∈ Set.range D₂.target.pts
        · obtain ⟨m, rfl⟩ := hPc
          have := hz m
          unfold angleCount at this
          omega
        · exact (TwoCs.side_le D₂ hsep₂ hγ₂ (tri_side_subset_frontier D₂.target 0 hP) hPc).1)
    have hF1 : F.card = 1 := le_antisymm h2 (Finset.card_pos.mpr ⟨e₀, Finset.mem_filter.mpr
      ⟨he₀, hγe⟩⟩)
    obtain ⟨eT, heT⟩ := Finset.card_eq_one.mp hF1
    exact twocs_core D₂ hsep₂ hγ₂ hirr₂ hαβ₂ hcorner hiv₂ hsingle part hcov hdisj eT heT

end TriangleTiling.ThreeAlpha
