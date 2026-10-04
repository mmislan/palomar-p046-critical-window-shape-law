module

public import proofs.RAFCriticalWindowQuantitative.BoundedRecords
public import proofs.RAFCriticalWindowQuantitative.FiniteRepair

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold MeasureTheory unitInterval
open scoped ENNReal

def escapedMissing (B : ℕ) (v : List Bool) : Set SplitField :=
  {ω | (∃ w, B < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w) ∧
    ¬ FiniteReversibleGenerated B 2 (currySplitField ω) v}

theorem finite_missing_determined (B : ℕ) (v : List Bool) :
    SplitPrefixDetermined (splitPrefixCoordinates B)
      {ω | ¬ FiniteReversibleGenerated B 2 (currySplitField ω) v} := by
  intro ω η he
  have ht (x y : SplitField)
      (hxy : ∀ z ∈ splitPrefixCoordinates B, x z = y z)
      (hg : FiniteReversibleGenerated B 2 (currySplitField x) v) :
      FiniteReversibleGenerated B 2 (currySplitField y) v := by
    apply finiteReversibleGenerated_transfer_prefix (M := B) le_rfl ?_ hg
    intro w hw k hk
    exact hxy (w,k) ((mem_splitPrefixCoordinates _ _).mpr ⟨hw,hk⟩)
  exact not_congr ⟨ht ω η he, ht η ω (fun z hz => (he z hz).symm)⟩

theorem escape_mem_record_atoms {B : ℕ} (hB : 2 ≤ B) {ω : SplitField}
    (h : ∃ w, B < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w) :
    ω ∈ ⋃ i : RecordPrefixIndex, recordPrefixAtom B i := by
  have hex : ∃ M, B < M ∧ currySplitField ω ∈ reversibleRecordEvent 2 M := by
    obtain ⟨w,hw,_,hg⟩ := escape_has_bounded_record hB h
    exact ⟨w.length,hw,w,rfl,hg⟩
  let M := Nat.find hex
  have hrec : currySplitField ω ∈ firstRecordEvent 2 B M := by
    refine ⟨(Nat.find_spec hex).1,(Nat.find_spec hex).2,?_⟩
    intro k hBk hk hr
    exact Nat.find_min hex hk ⟨hBk,hr⟩
  exact Set.mem_iUnion.mpr ⟨⟨M,fun z => ω z.val⟩,hrec,fun _ => rfl⟩

theorem first_record_cap {B M : ℕ} (hB : 2 ≤ B) {ω : SplitField}
    (h : currySplitField ω ∈ firstRecordEvent 2 B M) : M ≤ 2*B := by
  obtain ⟨w,hw,hg⟩ := h.2.1
  have hBM := h.1
  have he : ∃ w, B < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w :=
    ⟨w,by omega,finiteReversibleGenerated_to_infinite hg⟩
  obtain ⟨v,hv,hvB,hvg⟩ := escape_has_bounded_record hB he
  by_contra hn
  exact h.2.2 v.length hv (by omega) ⟨v,rfl,hvg⟩

/-- The deterministic-cap contraction; no conditioning on future escape. -/
theorem escaped_missing_contraction (a : I) (v : List Bool) (hv : 0 < v.length)
    (B : ℕ) (hB : 2 ≤ B) :
    infiniteSplitPi a (escapedMissing (2*B+v.length) v) ≤
      infiniteSplitPi a (escapedMissing B v) * (1-(toNNReal a : ENNReal)^(v.length+1)) := by
  let C : Set SplitField := {ω | ¬ FiniteReversibleGenerated B 2 (currySplitField ω) v}
  let D : RecordPrefixIndex → Set SplitField := fun i => C ∩ recordPrefixAtom B i
  have hC := finite_missing_determined B v
  have hmeasC := measurableSet_of_splitPrefixDetermined _ C hC
  have hmeas (i : RecordPrefixIndex) : MeasurableSet (D i) :=
    hmeasC.inter (measurableSet_of_splitPrefixDetermined _ _ (recordPrefixAtom_determined B i))
  have hdis : Pairwise (fun i j => Disjoint (D i) (D j)) := by
    intro i j hij
    exact (recordPrefixAtoms_disjoint B hij).mono Set.inter_subset_right Set.inter_subset_right
  have hpiece (i : RecordPrefixIndex) :
      infiniteSplitPi a (escapedMissing (2*B+v.length) v ∩ D i) ≤
        infiniteSplitPi a (D i) * (1-(toNNReal a : ENNReal)^(v.length+1)) := by
    by_cases hn : (D i).Nonempty
    · obtain ⟨ω,hω⟩ := hn
      have hBM : B < i.1 := hω.2.1.1
      have hMB := first_record_cap hB hω.2.1
      obtain ⟨w,hw,hBw,hrecord⟩ := recordPrefixAtom_word B i ⟨ω,hω.2⟩
      have hd : SplitPrefixDetermined (splitPrefixCoordinates w.length) (D i) := by
        rw [hw]
        intro η ξ he
        apply and_congr
        · apply hC
          intro z hz
          have hz' := (mem_splitPrefixCoordinates B z).mp hz
          exact he z ((mem_splitPrefixCoordinates i.1 z).mpr ⟨by omega,by omega⟩)
        · exact recordPrefixAtom_determined B i η ξ he
      apply (measure_mono (show escapedMissing (2*B+v.length) v ∩ D i ⊆
        D i ∩ {η | ¬ FiniteReversibleGenerated (2*B+v.length) 2 (currySplitField η) v}
        from fun η hη => ⟨hη.2,hη.1.2⟩)).trans
      exact finite_record_failure_bound a w v (by omega) hv (2*B+v.length)
        (by omega) (D i) hd (fun η hη => hrecord η hη.2)
    · have he : D i = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
      simp [he]
  have hcover : escapedMissing (2*B+v.length) v ⊆
      ⋃ i : RecordPrefixIndex, escapedMissing (2*B+v.length) v ∩ D i := by
    intro ω hω
    obtain ⟨w,hw,hg⟩ := hω.1
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (escape_mem_record_atoms hB ⟨w,by omega,hg⟩)
    exact Set.mem_iUnion.mpr ⟨i,hω,
      (fun hgen => hω.2 (finiteReversibleGenerated_mono_cap (by omega) hgen)),hi⟩
  have hsub : (⋃ i : RecordPrefixIndex, D i) ⊆ escapedMissing B v := by
    intro ω hω
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hω
    obtain ⟨w,hw,hg⟩ := hi.2.1.2.1
    exact ⟨⟨w,by have hb := hi.2.1.1; omega,finiteReversibleGenerated_to_infinite hg⟩,hi.1⟩
  calc
    _ ≤ infiniteSplitPi a (⋃ i : RecordPrefixIndex, escapedMissing (2*B+v.length) v ∩ D i) := measure_mono hcover
    _ ≤ ∑' i : RecordPrefixIndex, infiniteSplitPi a (escapedMissing (2*B+v.length) v ∩ D i) := measure_iUnion_le _
    _ ≤ ∑' i : RecordPrefixIndex, infiniteSplitPi a (D i) *
        (1-(toNNReal a : ENNReal)^(v.length+1)) := ENNReal.tsum_le_tsum hpiece
    _ = infiniteSplitPi a (⋃ i : RecordPrefixIndex, D i) *
        (1-(toNNReal a : ENNReal)^(v.length+1)) := by
      rw [ENNReal.tsum_mul_right,measure_iUnion hdis hmeas]
    _ ≤ _ := mul_le_mul_left (measure_mono hsub) _

end RAFCriticalWindowQuantitative
