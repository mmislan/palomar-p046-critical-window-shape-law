module

public import proofs.HordijkSteelThreshold.ScalarHistoryDistribution

@[expose] public section

namespace RAFEmergenceApprox.Generic
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold
open RAF.Concrete

variable {X R : Type*} [Fintype X] [Fintype R]

noncomputable def colLaw (X : Type*) [Fintype X] (p : I) : Measure (X → Prop) :=
  Measure.pi (fun _ : X => ambientCoordLaw p)

instance colLaw_probability (p : I) : IsProbabilityMeasure (colLaw X p) := by
  unfold colLaw
  infer_instance

noncomputable def law (p : R → I) : Measure (R → X → Prop) :=
  Measure.pi (fun r => colLaw X (p r))

instance law_probability (p : R → I) : IsProbabilityMeasure (law (X := X) p) := by
  unfold law
  infer_instance

def catalystPoolOpen (ω : R → X → Prop) (C : Finset X) (r : R) : Prop :=
  ∃ x ∈ C, ω r x

def catalystColumnHistory (ω : R → X → Prop) (C : ℕ → Finset X)
    (r : R) (T d : ℕ) : Prop :=
  decreasingHistory (fun t => catalystPoolOpen ω (C t) r) T d

theorem closed_probability (p : I) (C : Finset X) :
    colLaw X p {v | ¬ ∃ x ∈ C, v x} = (toNNReal (σ p) : ENNReal)^C.card := by
  have hi := iIndepFun_pi (fun _ : X => (measurable_id : Measurable (id : Prop → Prop)).aemeasurable)
      (μ := fun _ : X => ambientCoordLaw p)
  change iIndepFun (fun i (ω : X → Prop) => ω i) (Measure.pi (fun _ : X => ambientCoordLaw p)) at hi
  have hp := hi.measure_inter_preimage_eq_mul C
    (sets := fun _ : X => ({False} : Set Prop)) (fun _ _ => MeasurableSet.singleton False)
  have he : {v : X → Prop | ¬ ∃ x ∈ C, v x} =
      ⋂ x ∈ C, (fun v : X → Prop => v x) ⁻¹' {False} := by
    ext v
    simp
  rw [he]
  change (Measure.pi (fun _ : X => ambientCoordLaw p)) _ = _
  rw [hp]
  have hf (x : X) : (Measure.pi (fun _ : X => ambientCoordLaw p))
      ((fun v : X → Prop => v x) ⁻¹' {False}) = (toNNReal (σ p) : ENNReal) := by
    rw [← Measure.map_apply (measurable_pi_apply x) (MeasurableSet.singleton False),
      (measurePreserving_eval (fun _ : X => ambientCoordLaw p) x).map_eq]
    exact ambientCoordLaw_false p
  simp_rw [hf]
  exact Finset.prod_const _

theorem column_history_probability (p : I) (C : ℕ → Finset X) (hC : Antitone C)
    (T d : ℕ) (hd : d ≤ T+1) :
    colLaw X p {v | decreasingHistory (fun t => ∃ x ∈ C t, v x) T d} =
      columnHistoryWeight (toNNReal (σ p)) (fun t => (C t).card) T d := by
  have hm (v : X → Prop) (a b : ℕ) (hab : a ≤ b) :
      (∃ x ∈ C b, v x) → ∃ x ∈ C a, v x := by
    rintro ⟨x,hx,hv⟩
    exact ⟨x,hC hab hx,hv⟩
  by_cases hz : d = 0
  · subst d
    simp only [columnHistoryWeight, ↓reduceIte]
    have he : {v : X → Prop | decreasingHistory (fun t => ∃ x ∈ C t, v x) T 0} =
        {v | ¬ ∃ x ∈ C 0, v x} := by
      ext v
      exact decreasingHistory_zero_iff _ _ (hm v)
    rw [he,closed_probability]
  · by_cases hs : T < d
    · have hd' : d = T+1 := by omega
      subst d
      simp only [columnHistoryWeight, ite_eq_right hz, ite_eq_left hs]
      have he : {v : X → Prop | decreasingHistory (fun t => ∃ x ∈ C t, v x) T (T+1)} =
          {v | ¬ ∃ x ∈ C T, v x}ᶜ := by
        ext v
        simpa only [Set.mem_ofPred_eq,Set.mem_compl_iff,not_not] using
          decreasingHistory_survives_iff _ _ (hm v)
      rw [he,measure_compl (Set.toFinite _).measurableSet (measure_ne_top _ _),measure_univ,closed_probability]
    · simp only [columnHistoryWeight, ite_eq_right hz, ite_eq_right hs]
      have he : {v : X → Prop | decreasingHistory (fun t => ∃ x ∈ C t, v x) T d} =
          {v | ¬ ∃ x ∈ C d, v x} \ {v | ¬ ∃ x ∈ C (d-1), v x} := by
        ext v
        simpa only [Set.mem_ofPred_eq,Set.mem_sdiff,not_not] using
          decreasingHistory_dies_iff _ _ _ (by omega) (by omega) (hm v)
      have hsub : {v : X → Prop | ¬ ∃ x ∈ C (d-1), v x} ⊆
          {v | ¬ ∃ x ∈ C d, v x} := by
        intro v hv hp
        exact hv (hm v (d-1) d (by omega) hp)
      rw [he,measure_sdiff hsub (Set.toFinite _).measurableSet.nullMeasurableSet
        (measure_ne_top _ _),closed_probability,closed_probability]

theorem measure_catalystHistories (p : R → I) (C : ℕ → Finset X) (hC : Antitone C)
    (S : Finset R) (T : ℕ) (death : R → ℕ) (hd : ∀ r ∈ S, death r ≤ T+1) :
    law (X := X) p {ω | ∀ r ∈ S, catalystColumnHistory ω C r T (death r)} =
      ∏ r ∈ S, columnHistoryWeight (toNNReal (σ (p r))) (fun t => (C t).card) T (death r) := by
  let E := fun r => {v : X → Prop | decreasingHistory (fun t => ∃ x ∈ C t, v x) T (death r)}
  have hi := iIndepFun_pi (fun _ : R => (measurable_id : Measurable (id : (X → Prop) → (X → Prop))).aemeasurable)
      (μ := fun r => colLaw X (p r))
  change iIndepFun (fun r (ω : R → X → Prop) => ω r) (Measure.pi (fun r => colLaw X (p r))) at hi
  have he : {ω : R → X → Prop | ∀ r ∈ S, catalystColumnHistory ω C r T (death r)} =
      ⋂ r ∈ S, (fun ω : R → X → Prop => ω r) ⁻¹' E r := by
    ext ω
    simp [E,catalystColumnHistory,catalystPoolOpen]
  rw [he]
  change (Measure.pi (fun r => colLaw X (p r))) _ = _
  rw [hi.measure_inter_preimage_eq_mul S (sets := E) (fun r _ => (Set.toFinite (E r)).measurableSet)]
  apply Finset.prod_congr rfl
  intro r hr
  change (Measure.pi (fun r => colLaw X (p r))) ((fun ω => ω r) ⁻¹' E r) = _
  rw [← Measure.map_apply (measurable_pi_apply r) (Set.toFinite (E r)).measurableSet,
    (measurePreserving_eval (fun r => colLaw X (p r)) r).map_eq]
  exact column_history_probability (p r) C hC T (death r) (hd r hr)

theorem measure_catalystHistories_eq_of_card (p : R → I)
    (C D : ℕ → Finset X) (hC : Antitone C) (hD : Antitone D)
    (hcard : ∀ t, (C t).card = (D t).card)
    (S : Finset R) (T : ℕ) (death : R → ℕ) (hd : ∀ r ∈ S, death r ≤ T+1) :
    law (X := X) p {ω | ∀ r ∈ S, catalystColumnHistory ω C r T (death r)} =
      law (X := X) p {ω | ∀ r ∈ S, catalystColumnHistory ω D r T (death r)} := by
  rw [measure_catalystHistories p C hC S T death hd,
    measure_catalystHistories p D hD S T death hd]
  simp_rw [hcard]

noncomputable def catalystActive  (ω : R → X → Prop)
    (C : Finset X) : Finset R := by
  classical
  exact Finset.univ.filter (catalystPoolOpen ω C)

omit [Fintype X] in
@[simp] theorem mem_catalystActive  (ω : R → X → Prop)
    (C : Finset X) (r : R) :
    r ∈ catalystActive ω C ↔ catalystPoolOpen ω C r := by
  classical
  simp [catalystActive]

omit [Fintype X] in
theorem catalystActive_mono  (ω : R → X → Prop) :
    Monotone (catalystActive ω) := by
  intro C D h r hr
  obtain ⟨x, hx, hω⟩ := (mem_catalystActive ω C r).mp hr
  exact (mem_catalystActive ω D r).mpr ⟨x, h hx, hω⟩

/-- Convert a prescribed process history into fixed column constraints.
The transform can be identity (source) or cardinality-indexed prefixes. -/
theorem peeling_event_eq_column_histories 
    (transform : Finset X → Finset X)
    (closure : Finset R → Finset X)
    (history : ℕ → Finset R) (T : ℕ) (death : R → ℕ)
    (hdeath : ∀ r t, t ≤ T → (r ∈ history t ↔ t < death r)) :
    {ω : R → X → Prop | ∀ t ≤ T,
      peelingActiveAt (fun C => catalystActive ω (transform C)) closure t = history t} =
    {ω | ∀ r ∈ (Finset.univ : Finset R),
      catalystColumnHistory ω (fun t => transform (prescribedPoolAt closure history t))
        r T (death r)} := by
  ext ω
  simp only [Set.mem_ofPred_eq, peeling_history_iff, Finset.mem_univ, forall_const]
  constructor
  · intro h r t ht
    rw [← hdeath r t ht, ← h t ht, mem_catalystActive]
  · intro h t ht
    apply Finset.ext
    intro r
    rw [mem_catalystActive]
    exact (h r t ht).trans (hdeath r t ht).symm

/-- The source process and its ordered-initialSegment replacement give exactly the
same probability to every prescribed decreasing active-set history.
The initialSegment assumptions are deterministic; adaptive independence is not assumed. -/
theorem peeling_history_probability_eq_prefix (p : R → I)
    (closure : Finset R → Finset X) (hclosure : Monotone closure)
    (initialSegment : ℕ → Finset X) (hprefix : Monotone initialSegment)
    (hcard : ∀ k ≤ Fintype.card X, (initialSegment k).card = k)
    (history : ℕ → Finset R) (hhistory : Antitone history) (T : ℕ) :
    law (X := X) p {ω | ∀ t ≤ T,
      peelingActiveAt (catalystActive ω) closure t = history t} =
    law (X := X) p {ω | ∀ t ≤ T,
      peelingActiveAt (fun C => catalystActive ω (initialSegment C.card)) closure t = history t} := by
  classical
  have hd : ∀ r : R, ∃ d ≤ T + 1,
      ∀ t ≤ T, r ∈ history t ↔ t < d := by
    intro r
    exact exists_history_death (fun t => r ∈ history t) T
      (fun _ _ hab hr => hhistory hab hr)
  choose death hbound hpattern using hd
  have he := peeling_event_eq_column_histories id closure history T death hpattern
  have hp := peeling_event_eq_column_histories
    (fun C => initialSegment C.card) closure history T death hpattern
  change {ω | ∀ t ≤ T, peelingActiveAt (catalystActive ω) closure t = history t} =
      {ω | ∀ r ∈ (Finset.univ : Finset R),
        catalystColumnHistory ω (prescribedPoolAt closure history) r T (death r)} at he
  rw [he, hp]
  have hc := prescribedPoolAt_antitone closure hclosure history hhistory
  apply measure_catalystHistories_eq_of_card p _ _ hc
  · intro a b hab
    exact hprefix (Finset.card_le_card (hc hab))
  · intro t
    exact (hcard _ (Finset.card_le_univ _)).symm
  · intro r _
    exact hbound r

theorem history_clamp_antitone_of_match {R : Type*}
    (A H : ℕ → Finset R) (hA : Antitone A) (T : ℕ)
    (hmatch : ∀ t ≤ T, A t = H t) :
    Antitone (fun t => H (min t T)) := by
  intro a b hab
  change H (min b T) ⊆ H (min a T)
  rw [← hmatch (min b T) (min_le_right _ _),
    ← hmatch (min a T) (min_le_right _ _)]
  exact hA (min_le_min_right T hab)

/-- Equality for arbitrary prescribed histories. Nondecreasing histories on
the finite horizon have probability zero for both processes. -/
theorem peeling_history_probability_eq_prefix_any (p : R → I)
    (closure : Finset R → Finset X) (hclosure : Monotone closure)
    (initialSegment : ℕ → Finset X) (hprefix : Monotone initialSegment)
    (hcard : ∀ k ≤ Fintype.card X, (initialSegment k).card = k)
    (history : ℕ → Finset R) (T : ℕ) :
    law (X := X) p {ω | ∀ t ≤ T,
      peelingActiveAt (catalystActive ω) closure t = history t} =
    law (X := X) p {ω | ∀ t ≤ T,
      peelingActiveAt (fun C => catalystActive ω (initialSegment C.card)) closure t = history t} := by
  classical
  by_cases hg : Antitone (fun t => history (min t T))
  · have h := peeling_history_probability_eq_prefix p closure hclosure
      initialSegment hprefix hcard (fun t => history (min t T)) hg T
    have he (A : ℕ → Finset R) :
        (∀ t ≤ T, A t = history (min t T)) ↔ (∀ t ≤ T, A t = history t) := by
      constructor <;> intro h t ht <;> simpa only [min_eq_left ht] using h t ht
    simpa only [he] using h
  · have hs : {ω : R → X → Prop | ∀ t ≤ T,
        peelingActiveAt (catalystActive ω) closure t = history t} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω h
      exact hg (history_clamp_antitone_of_match _ history
        (peelingActiveAt_antitone _ closure (catalystActive_mono ω) hclosure) T h)
    have hp : {ω : R → X → Prop | ∀ t ≤ T,
        peelingActiveAt (fun C => catalystActive ω (initialSegment C.card)) closure t = history t} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω h
      have hm : Monotone (fun C : Finset X =>
          catalystActive ω (initialSegment C.card)) := by
        intro C D hCD
        exact catalystActive_mono ω (hprefix (Finset.card_le_card hCD))
      exact hg (history_clamp_antitone_of_match _ history
        (peelingActiveAt_antitone _ closure hm hclosure) T h)
    rw [hs, hp]


theorem activeTrace_map_eq_scalar (p : R → I)
    (closure : Finset R → Finset X)
    (hclosure : Monotone closure) (T : ℕ) :
    (law (X := X) p).map (fun ω => activeTrace (catalystActive ω) closure T) =
      (law (X := X) p).map (fun ω => activeTrace
        (fun C => catalystActive ω (finiteInitialSegment X C.card)) closure T) := by
  apply Measure.ext_of_singleton
  intro H
  rw [Measure.map_apply (measurable_of_finite _) (MeasurableSet.singleton H),
    Measure.map_apply (measurable_of_finite _) (MeasurableSet.singleton H)]
  have hs := peeling_history_probability_eq_prefix_any p closure hclosure
    (finiteInitialSegment X) (finiteInitialSegment_mono X)
    (card_finiteInitialSegment X) (traceHistory H) T
  simpa only [Set.preimage, Set.mem_singleton_iff, activeTrace_eq_iff] using hs


end RAFEmergenceApprox.Generic
