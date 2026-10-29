/-
The pigeonhole on a wall, for `lemma:twocs` ("the pigeon-hole argument" of its proof).

The tiles along a wall `PR` with their edges inside it are `n ≥ 1`, and their edges meet at `n - 1`
points strictly inside `PR`. If none of these edges is a `c` edge, each of those tiles has its `γ`
at an end of its edge; if none has it at `P` or `R`, and no point carries two `γ`, there are `n`
angles `γ` at `n - 1` points.
-/
import TriangleTiling.TwoCs.Wall
import TriangleTiling.TwoCs.Corners

namespace TriangleTiling.TwoCs

open Erdos634.Geometry Set

variable {N : ℕ} (D : CongruentDissection N) (hsep : AnglesSep D) {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}
  {P R : Plane}

include hsep in
open Classical in
/-- **The pigeonhole on a wall.** -/
theorem wall_gamma (hg : g ≠ 0) (hPR : P ≠ R) (hP : g P = c) (hR : g R = c)
    (hendP : ∀ e ∈ D.lineChain g c,
      P ∉ openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
    (hendR : ∀ e ∈ D.lineChain g c,
      R ∉ openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
    (hint : openSegment ℝ P R ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P R, ∀ i, y ∉ interior (D.tile i).carrier)
    (hnc : ∀ e ∈ D.lineChain g c, (D.tile e.1).edge e.2 ⊆ segment ℝ P R →
      (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) ≠ tileγ D)
    (hnoP : ∀ e ∈ D.lineChain g c, (D.tile e.1).edge e.2 ⊆ segment ℝ P R →
      (D.tile e.1).localAngle P ≠ tileγ D)
    (hnoR : ∀ e ∈ D.lineChain g c, (D.tile e.1).edge e.2 ⊆ segment ℝ P R →
      (D.tile e.1).localAngle R ≠ tileγ D)
    (hone : ∀ y ∈ openSegment ℝ P R, angleCount D y (tileγ D) ≤ 1) : False := by
  set S := (D.lineChain g c).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ P R)
  have hcov := chain_cover D.toDissection hg hPR hP hR hendP hendR hint hwall
  have hdisj : ∀ e₁ ∈ S, ∀ e₂ ∈ S, e₁ ≠ e₂ →
      ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton :=
    fun e₁ h₁ e₂ h₂ hne => chain_disj D.toDissection hg (Finset.mem_filter.mp h₁).1
      (Finset.mem_filter.mp h₂).1 hne
  set u : Fin N × Fin 3 → Plane := fun e => (D.tile e.1).pts e.2
  set v : Fin N × Fin 3 → Plane := fun e => (D.tile e.1).pts (e.2 + 1)
  have huv : ∀ e ∈ S, u e ≠ v e := fun e _ => tri_pts_succ_ne _ _
  have hchain := segment_chain_endpoints P R hPR S u v huv hcov hdisj
  set Eint := (S.image u ∪ S.image v).filter fun x => x ≠ P ∧ x ≠ R
  -- Each tile of `S` has its `γ` at an end of its edge.
  have hγend : ∀ e ∈ S, (D.tile e.1).localAngle (u e) = tileγ D ∨
      (D.tile e.1).localAngle (v e) = tileγ D := by
    intro e he
    obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
    exact corner_at_endpoint D hsep e.1 e.2 (Or.inr (Or.inr rfl)) (hnc e he1 he2)
  let φ : Fin N × Fin 3 → Plane := fun e =>
    if (D.tile e.1).localAngle (u e) = tileγ D then u e else v e
  have hφγ : ∀ e ∈ S, (D.tile e.1).localAngle (φ e) = tileγ D := by
    intro e he
    simp only [φ]
    split_ifs with h
    · exact h
    · exact (hγend e he).resolve_left h
  have hφuv : ∀ e, φ e = u e ∨ φ e = v e := by
    intro e; simp only [φ]; split_ifs <;> simp
  have hφseg : ∀ e ∈ S, φ e ∈ segment ℝ P R := by
    intro e he
    apply (Finset.mem_filter.mp he).2
    rcases hφuv e with h | h <;> rw [h]
    · exact left_mem_segment _ _ _
    · exact right_mem_segment _ _ _
  have hφE : ∀ e ∈ S, φ e ∈ Eint := by
    intro e he
    obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
    · rcases hφuv e with h | h <;> rw [h]
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ he)
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)
    · intro h; exact hnoP e he1 he2 (h ▸ hφγ e he)
    · intro h; exact hnoR e he1 he2 (h ▸ hφγ e he)
  -- `φ` is injective on `S`.
  have hinj : Set.InjOn φ S := by
    intro e he e' he' heq
    by_contra hne
    by_cases h1 : e.1 = e'.1
    · have h2 : e.2 ≠ e'.2 := fun h2 => hne (Prod.ext h1 h2)
      exact tri_two_edges_on_segment (D.tile e.1) h2 (Finset.mem_filter.mp he).2
        (h1 ▸ (Finset.mem_filter.mp he').2)
    · have hE := Finset.mem_filter.mp (hφE e he)
      have hopen : φ e ∈ openSegment ℝ P R := by
        rw [← insert_endpoints_openSegment] at *
        rcases (hφseg e he) with h | h | h
        · exact absurd h hE.2.1
        · exact absurd h hE.2.2
        · exact h
      have hle := hone _ hopen
      exact h1 (eq_of_angleCount_le_one D hle (hφγ e he) (heq ▸ hφγ e' he'))
  have hcard : S.card ≤ Eint.card := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card fun x hx => by
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      exact hφE e he
  have := hchain.1
  omega

end TriangleTiling.TwoCs
