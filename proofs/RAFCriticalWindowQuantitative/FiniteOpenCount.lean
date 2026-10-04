module

public import proofs.HordijkSteelThreshold.StaticEventContinuity
public import proofs.RAFCriticalWindowQuantitative.SparseClosure

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 100000

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

theorem finite_support_open_probability (J : Type*) [Fintype J] (a : I) (T : Finset J) :
    (Measure.pi (fun _ : J => ambientCoordLaw a)) {ω | ∀ j ∈ T, ω j} = (toNNReal a : ENNReal)^T.card := by
  have he : {ω : J → Prop | ∀ j ∈ T, ω j} =
      (T : Set J).pi (fun _ => ({True} : Set Prop)) := by
    ext ω
    simp
  rw [he, Measure.pi_pi_finset]
  simp [ambientCoordLaw]
theorem finite_many_open_probability (J : Type*) [Fintype J] (a : I) (r : ℕ) :
    (Measure.pi (fun _ : J => ambientCoordLaw a))
      {ω | r ≤ (Finset.univ.filter (fun j : J => ω j)).card} ≤
      ((Fintype.card J).choose r : ENNReal)*(toNNReal a : ENNReal)^r := by
  let μ := Measure.pi (fun _ : J => ambientCoordLaw a)
  let P := (Finset.univ : Finset J).powersetCard r
  have hs : {ω : J → Prop | r ≤ (Finset.univ.filter (fun j : J => ω j)).card} ⊆
      ⋃ T ∈ P, {ω | ∀ j ∈ T, ω j} := by
    intro ω hω
    obtain ⟨T,hT,hcard⟩ := Finset.exists_subset_card_eq hω
    refine Set.mem_iUnion.mpr ⟨T,Set.mem_iUnion.mpr ⟨?_,?_⟩⟩
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hcard⟩
    · intro j hj
      exact (Finset.mem_filter.mp (hT hj)).2
  calc
    _ ≤ μ (⋃ T ∈ P, {ω | ∀ j ∈ T, ω j}) := measure_mono hs
    _ ≤ ∑ T ∈ P, μ {ω | ∀ j ∈ T, ω j} := measure_biUnion_finset_le _ _
    _ = ∑ _T ∈ P, (toNNReal a : ENNReal)^r := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [finite_support_open_probability, (Finset.mem_powersetCard.mp hT).2]
    _ = _ := by simp [P]

end RAFCriticalWindowQuantitative
