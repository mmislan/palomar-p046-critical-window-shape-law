module

public import proofs.RAFEmergenceApprox.GenericHistory

@[expose] public section

namespace RAFReactionQuotient
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold

variable {R J : Type*} [Fintype R]

def fieldOR (π : R → J) (ω : R → Prop) (j : J) : Prop :=
  ∃ r, π r = j ∧ ω r

/-- Predicates on disjoint quotient fibres are independent, including a whole
family of other fibres. -/
theorem fibre_event_indep (π : R → J) (p : I) (E : J → Prop → Prop)
    (j : J) (S : Finset J) (hj : j ∉ S) :
    IndepFun (fun ω : R → Prop => E j (fieldOR π ω j))
      (fun ω => ∀ k ∈ S, E k (fieldOR π ω k))
      (RAFEmergenceApprox.Generic.colLaw R p) := by
  let B := Finset.univ.filter (fun r : R => π r = j)
  let D := Finset.univ.filter (fun r : R => π r ∈ S)
  have hd : Disjoint B D := by
    apply Finset.disjoint_left.mpr
    intro r hr hs
    exact hj ((Finset.mem_filter.mp hr).2 ▸ (Finset.mem_filter.mp hs).2)
  have hi := iIndepFun_pi
    (fun _ : R => (measurable_id : Measurable (id : Prop → Prop)).aemeasurable)
    (μ := fun _ : R => ambientCoordLaw p)
  have ht := hi.indepFun_finset B D hd (fun _ => measurable_pi_apply _)
  let f : (B → Prop) → Prop := fun v => E j (∃ r : B, v r)
  let g : (D → Prop) → Prop := fun v => ∀ k ∈ S, E k (∃ r : D, π r.val = k ∧ v r)
  have he := ht.comp (measurable_of_finite f) (measurable_of_finite g)
  have hf : (fun ω : R → Prop => f (fun r : B => ω r.val)) =
      (fun ω => E j (fieldOR π ω j)) := by
    funext ω
    dsimp [f]
    congr 1
    apply propext
    simp [B, fieldOR]
  have hg : (fun ω : R → Prop => g (fun r : D => ω r.val)) =
      (fun ω => ∀ k ∈ S, E k (fieldOR π ω k)) := by
    funext ω
    apply propext
    apply forall_congr'
    intro k
    apply forall_congr'
    intro hk
    have hh : (∃ r : D, π r.val = k ∧ ω r.val) ↔ fieldOR π ω k := by
      constructor
      · rintro ⟨r,hr,ho⟩
        exact ⟨r.val,hr,ho⟩
      · rintro ⟨r,hr,ho⟩
        exact ⟨⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr.symm ▸ hk⟩⟩,hr,ho⟩
    dsimp [g]
    rw [propext hh]
  change IndepFun (fun ω : R → Prop => f (fun r : B => ω r.val))
    (fun ω => g (fun r : D => ω r.val)) _ at he
  rw [hf,hg] at he
  exact he

theorem fibre_events_product (π : R → J) (p : I) (E : J → Prop → Prop)
    (S : Finset J) :
    RAFEmergenceApprox.Generic.colLaw R p {ω | ∀ j ∈ S, E j (fieldOR π ω j)} =
      ∏ j ∈ S, RAFEmergenceApprox.Generic.colLaw R p {ω | E j (fieldOR π ω j)} := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert j S hj ih =>
    have hi := (fibre_event_indep π p E j S hj).measure_inter_preimage_eq_mul
      {True} {True} (MeasurableSet.singleton True) (MeasurableSet.singleton True)
    have he : {ω : R → Prop | ∀ k ∈ insert j S, E k (fieldOR π ω k)} =
        {ω | E j (fieldOR π ω j)} ∩ {ω | ∀ k ∈ S, E k (fieldOR π ω k)} := by
      ext ω
      simp
    rw [he, Finset.prod_insert hj]
    simpa only [Set.preimage, Set.mem_singleton_iff, eq_iff_iff, iff_true, ih] using hi

theorem fieldOR_independent (π : R → J) (p : I) :
    iIndepFun (fun j (ω : R → Prop) => fieldOR π ω j)
      (RAFEmergenceApprox.Generic.colLaw R p) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  have he : (⋂ j ∈ S, (fun ω : R → Prop => fieldOR π ω j) ⁻¹' sets j) =
      {ω | ∀ j ∈ S, fieldOR π ω j ∈ sets j} := by
    ext ω
    simp
  rw [he]
  exact fibre_events_product π p (fun j z => z ∈ sets j) S

theorem fieldOR_closed_probability (π : R → J) (p : I) (j : J) :
    RAFEmergenceApprox.Generic.colLaw R p {ω | ¬ fieldOR π ω j} =
      (toNNReal (σ p) : ENNReal) ^ (Finset.univ.filter (fun r => π r = j)).card := by
  have he : {ω : R → Prop | ¬ fieldOR π ω j} =
      {ω | ¬ ∃ r ∈ Finset.univ.filter (fun r => π r = j), ω r} := by
    ext ω
    simp [fieldOR]
  rw [he]
  exact RAFEmergenceApprox.Generic.closed_probability _ _

end RAFReactionQuotient
