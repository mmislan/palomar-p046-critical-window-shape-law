module

public import proofs.RAFCriticalWindowQuantitative.RecordIteration
public import proofs.RAFCriticalWindowQuantitative.EffectiveSeedSurvival

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold MeasureTheory unitInterval RAF.Polymer
open scoped ENNReal

/-- Literal infinite escape probability; first escape gives its finite cap 2K. -/
noncomputable def splitEscapeProbability (a : I) (K : ℕ) : ENNReal :=
  infiniteSplitPi a {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w}

theorem explicit_split_truncation (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m : ℕ) (hm : 2 ≤ m) (a : I) (ha : rationalParameter q hq.le hq1 ≤ a) (r : ℕ) :
    let L := 10*seedIndex q hq hq1 m
    splitEscapeProbability a (recordCap L r) ≤ staticSurvival a + (m : ENNReal)⁻¹ +
      ((actualBinaryWords L).card : ENNReal) * (1-(toNNReal a : ENNReal)^(L+1))^r := by
  let L := 10*seedIndex q hq hq1 m
  let K := recordCap L r
  let E : Set SplitField := {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w}
  let H : Set SplitField := {ω | ∀ v ∈ actualBinaryWords L, FiniteReversibleGenerated K 2 (currySplitField ω) v}
  let G : Set SplitField := {ω | ∀ v ∈ actualBinaryWords L, InfiniteReversibleGenerated 2 (currySplitField ω) v}
  have hseed : ∀ v ∈ actualBinaryWords L, 0 < v.length ∧ v.length ≤ L := by
    intro v hv
    have hh := (mem_actualBinaryWords v L).mp hv
    exact ⟨List.length_pos_iff.mpr hh.1,hh.2⟩
  have hbad : infiniteSplitPi a (E ∩ Hᶜ) ≤
      ((actualBinaryWords L).card : ENNReal) * (1-(toNNReal a : ENNReal)^(L+1))^r :=
    finite_seed_failure a (actualBinaryWords L) L hseed r
  have hgood : infiniteSplitPi a H ≤ staticSurvival a + (m : ENNReal)⁻¹ := by
    have hi := effective_seed_probability_le_survival q hq hq1 m hm a ha
    have hmeas : MeasurableSet {field : InfiniteSplitEnvironment |
        ∀ v ∈ actualBinaryWords L, InfiniteReversibleGenerated 2 field v} := by
      have he : {field : InfiniteSplitEnvironment |
          ∀ v ∈ actualBinaryWords L, InfiniteReversibleGenerated 2 field v} =
          ⋂ v ∈ actualBinaryWords L, {field | InfiniteReversibleGenerated 2 field v} := by
        ext field
        simp
      rw [he]
      exact MeasurableSet.biInter (Finset.countable_toSet _) (fun v _ =>
        measurableSet_infiniteReversibleGenerated 2 v)
    rw [infiniteStaticMeasure, Measure.map_apply measurable_currySplitField
      hmeas] at hi
    apply (measure_mono (show H ⊆ G from ?_)).trans hi
    intro ω hω v hv
    exact finiteReversibleGenerated_to_infinite (hω v hv)
  have hs : E ⊆ (E ∩ Hᶜ) ∪ H := by
    intro ω hω
    by_cases hh : ω ∈ H
    · exact Or.inr hh
    · exact Or.inl ⟨hω,hh⟩
  calc
    splitEscapeProbability a K ≤ infiniteSplitPi a ((E ∩ Hᶜ) ∪ H) := measure_mono hs
    _ ≤ infiniteSplitPi a (E ∩ Hᶜ) + infiniteSplitPi a H := measure_union_le _ _
    _ ≤ _ := by simpa only [add_comm] using add_le_add hbad hgood

end RAFCriticalWindowQuantitative
