module

public import proofs.RAF.Frankl.Antimatroid

@[expose] public section

namespace OverlapCorrectedRAF.Core

open RAF RAF.Frankl

variable {M R J : Type*} [DecidableEq M] [DecidableEq R] [DecidableEq J]

/-- A reaction-support core records only the deterministic structural part:
nonemptiness and food generation.  Catalytic activation is a separate event. -/
def IsReactionSupportCore (Q : CRS M R) (S : Finset R) : Prop :=
  S.Nonempty ∧ FoodGenerated Q S

/-- An irrRAF is minimal by reaction support, not by a chosen catalyst witness. -/
def IsIrrRAF (Q : CRS M R) (C : Catalysis M R) (S : Finset R) : Prop :=
  IsRAF Q C S ∧ ∀ T : Finset R, T ⊂ S → ¬ IsRAF Q C T

/-- A catalytic witness selects one eligible catalyst for every reaction. -/
def IsCatalyticWitness (Q : CRS M R) (C : Catalysis M R)
    (S : Finset R) (w : R → M) : Prop :=
  ∀ r ∈ S, (∃ k, w r ∈ closureAt Q S k) ∧ C (w r) r

/-- The stronger, distinct notion that one molecule catalyses every reaction. -/
def IsSingleCatalystCore (Q : CRS M R) (C : Catalysis M R)
    (S : Finset R) : Prop :=
  IsReactionSupportCore Q S ∧
    ∃ x, (∃ k, x ∈ closureAt Q S k) ∧ ∀ r ∈ S, C x r

/-- For a food-generated support this finite set is exactly its food closure. -/
def coreMolecules (Q : CRS M R) (S : Finset R) : Finset M :=
  Q.food ∪ S.biUnion Q.outputs

/-- Independent catalysis channels used by a directed reaction support. -/
def coreChannels (chi : R → J) (S : Finset R) : Finset J :=
  S.image chi

/-- Exact activation event for a fixed support: every required channel fibre
has at least one coordinate whose molecule lies in the support closure. -/
def CoreHitEvent (Q : CRS M R) (chi : R → J)
    (Y : Finset (M × J)) (S : Finset R) : Prop :=
  ∀ j ∈ coreChannels chi S, ∃ x ∈ coreMolecules Q S, (x, j) ∈ Y

omit [DecidableEq R] in
theorem mem_coreMolecules_iff_reachable
    (Q : CRS M R) {S : Finset R} (hfg : FoodGenerated Q S) (x : M) :
    x ∈ coreMolecules Q S ↔ ∃ k, x ∈ closureAt Q S k := by
  constructor
  · intro hx
    simp only [coreMolecules, Finset.mem_union, Finset.mem_biUnion] at hx
    rcases hx with hxfood | ⟨r, hr, hxout⟩
    · exact ⟨0, hxfood⟩
    · exact output_mem_some_closureAt_of_foodGenerated Q hfg hr hxout
  · rintro ⟨k, hx⟩
    rcases mem_closureAt_imp_food_or_output Q S hx with hxfood | ⟨r, hr, hxout⟩
    · exact Finset.mem_union_left _ hxfood
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, hr, hxout⟩)

omit [DecidableEq R] in
/-- Closure-hit semantics for one fixed structural core.  Reactions sharing a
channel contribute only one hit constraint because their catalysis predicates
are the same channel coordinate predicate. -/
theorem isRAF_channel_iff_coreHitEvent
    (Q : CRS M R) (chi : R → J) (Y : Finset (M × J))
    {S : Finset R} (hcore : IsReactionSupportCore Q S) :
    IsRAF Q (fun x r => (x, chi r) ∈ Y) S ↔ CoreHitEvent Q chi Y S := by
  refine (isRAF_iff_foodGenerated_and_productGraph Q
    (fun x r => (x, chi r) ∈ Y) S).trans ?_
  constructor
  · rintro ⟨_, _, hcat⟩ j hj
    obtain ⟨r, hr, hrj⟩ := Finset.mem_image.mp hj
    subst j
    rcases hcat r hr with ⟨x, hxfood, hxy⟩ | ⟨u, hu, x, hxout, hxy⟩
    · exact ⟨x, Finset.mem_union_left _ hxfood, hxy⟩
    · exact ⟨x, Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨u, hu, hxout⟩), hxy⟩
  · intro hhit
    refine ⟨hcore.1, hcore.2, ?_⟩
    intro r hr
    obtain ⟨x, hx, hxy⟩ := hhit (chi r) (Finset.mem_image.mpr ⟨r, hr, rfl⟩)
    simp only [coreMolecules, Finset.mem_union, Finset.mem_biUnion] at hx
    rcases hx with hxfood | ⟨u, hu, hxout⟩
    · exact Or.inl ⟨x, hxfood, hxy⟩
    · exact Or.inr ⟨u, hu, x, hxout, hxy⟩

omit [DecidableEq R] in
/-- Every finite RAF contains an inclusion-minimal RAF support. -/
theorem exists_irraf_subset
    (Q : CRS M R) (C : Catalysis M R) {S : Finset R}
    (hraf : IsRAF Q C S) :
    ∃ T : Finset R, T ⊆ S ∧ IsIrrRAF Q C T := by
  classical
  let candidates : Finset (Finset R) := S.powerset.filter (IsRAF Q C)
  have hcandidates : candidates.Nonempty := by
    refine ⟨S, ?_⟩
    simp [candidates, hraf]
  obtain ⟨T, hTmem, hTmin⟩ :=
    Finset.exists_min_image candidates Finset.card hcandidates
  have hTdata := Finset.mem_filter.mp hTmem
  refine ⟨T, (Finset.mem_powerset.mp hTdata.1), hTdata.2, ?_⟩
  intro U hUT hUraf
  have hUS : U ⊆ S := (Finset.ssubset_iff_subset_ne.mp hUT).1.trans
    (Finset.mem_powerset.mp hTdata.1)
  have hUmem : U ∈ candidates := by
    simp [candidates, hUS, hUraf]
  have hcard := hTmin U hUmem
  exact (not_le_of_gt (Finset.card_lt_card hUT)) hcard

omit [DecidableEq R] in
theorem hasRAF_iff_exists_irraf (Q : CRS M R) (C : Catalysis M R) :
    (∃ S : Finset R, IsRAF Q C S) ↔
      ∃ S : Finset R, IsIrrRAF Q C S := by
  constructor
  · rintro ⟨S, hS⟩
    obtain ⟨T, _, hT⟩ := exists_irraf_subset Q C hS
    exact ⟨T, hT⟩
  · rintro ⟨S, hS⟩
    exact ⟨S, hS.1⟩

end OverlapCorrectedRAF.Core
