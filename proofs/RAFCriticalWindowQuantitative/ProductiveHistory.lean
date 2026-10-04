module

public import proofs.RAFCriticalWindowQuantitative.QuotientSparseClosure

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAF.Concrete RAF.Polymer RAFReactionQuotient OverlapCorrectedRAF.Source

def fullClosure {M R : Type*} [Fintype M] [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) : Finset M := revClosureAt Q S (Fintype.card M)

inductive ProductiveHistory {M R : Type*} [Fintype M] [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) : ℕ → Finset R → Prop
  | nil : ProductiveHistory Q S 0 ∅
  | step {k T r} : ProductiveHistory Q S k T → r ∈ S → r ∉ T →
      revClosureStep Q {r} (fullClosure Q T) ≠ fullClosure Q T →
      ProductiveHistory Q S (k+1) (insert r T)

theorem productive_extension {M R : Type*} [Fintype M] [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S T : Finset R) (x : M)
    (hx : x ∈ fullClosure Q S) (hnot : x ∉ fullClosure Q T) :
    ∃ r ∈ S, r ∉ T ∧ revClosureStep Q {r} (fullClosure Q T) ≠ fullClosure Q T := by
  let C := fullClosure Q T
  have hfixed : revClosureStep Q T C = C := closure_stable_at_card Q T
  have hg : revClosureStep Q S C ≠ C := by
    intro he
    have hall : ∀ k, revClosureAt Q S k ⊆ C := by
      intro k
      induction k with
      | zero => exact revClosureAt_mono_stage Q T (Nat.zero_le _)
      | succ k ih =>
        exact (revClosureStep_mono Q Finset.Subset.rfl ih).trans (Finset.subset_of_eq he)
    exact hnot (hall _ hx)
  have hex : ∃ r ∈ S, revClosureStep Q {r} C ≠ C := by
    by_contra h
    push Not at h
    apply hg
    apply Finset.Subset.antisymm _ Finset.subset_union_left
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact hy
    · obtain ⟨r,hr,hy⟩ := Finset.mem_biUnion.mp hy
      have hh : y ∈ revClosureStep Q {r} C :=
        Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r,Finset.mem_singleton_self _,hy⟩)
      rw [h r hr] at hh
      exact hh
  obtain ⟨r,hr,hgrow⟩ := hex
  refine ⟨r,hr,?_,hgrow⟩
  intro hrT
  apply hgrow
  apply Finset.Subset.antisymm _ Finset.subset_union_left
  exact (revClosureStep_mono Q (Finset.singleton_subset_iff.mpr hrT) Finset.Subset.rfl).trans
    (Finset.subset_of_eq hfixed)

theorem long_target_productive_history {M R : Type*} [Fintype M] [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (length : M → ℕ)
    (hbound : ∀ T x, x ∈ fullClosure Q T → length x ≤ 2^(T.card+1))
    (S : Finset R) (k : ℕ) (x : M) (hx : x ∈ fullClosure Q S)
    (hlen : 2^(k+1) < length x) :
    ∃ T, ProductiveHistory Q S k T ∧ T.card = k ∧ T ⊆ S := by
  induction k with
  | zero => exact ⟨∅,ProductiveHistory.nil,Finset.card_empty,Finset.empty_subset _⟩
  | succ k ih =>
    have hp : 2^(k+1) ≤ 2^(k+1+1) := Nat.pow_le_pow_right (by omega) (by omega)
    obtain ⟨T,hT,hcard,hTS⟩ := ih (hp.trans_lt hlen)
    have hnot : x ∉ fullClosure Q T := by
      intro hh
      have hb := hbound T x hh
      rw [hcard] at hb
      omega
    obtain ⟨r,hr,hrT,hgrow⟩ := productive_extension Q S T x hx hnot
    exact ⟨insert r T,ProductiveHistory.step hT hr hrT hgrow,
      by rw [Finset.card_insert_of_notMem hrT,hcard],Finset.insert_subset hr hTS⟩

theorem split_long_target_history (N k : ℕ) (S : Finset (Reaction N)) (x : Molecule N)
    (hx : x ∈ temporaryReactionClosure 2 S) (hlen : 2^(k+1) < molLength x) :
    ∃ T, ProductiveHistory (binaryPolymerCRS N 2) S k T ∧ T.card = k ∧ T ⊆ S := by
  apply long_target_productive_history _ molLength _ S k x _ hlen
  · intro T y hy
    apply sparse_closure_length N T y
    rwa [← computedClosure_eq]
  · rwa [← computedClosure_eq] at hx

theorem quotient_long_target_history (N k : ℕ) (S : Finset (RepositoryChannel N)) (x : Molecule N)
    (hx : x ∈ quotientClosure N 2 S) (hlen : 2^(k+1) < molLength x) :
    ∃ T, ProductiveHistory (repositoryCRS N 2) S k T ∧ T.card = k ∧ T ⊆ S := by
  have he (T : Finset (RepositoryChannel N)) : fullClosure (repositoryCRS N 2) T = quotientClosure N 2 T := by
    ext y
    rw [mem_quotientClosure]
    constructor
    · intro hy; exact ⟨Fintype.card (Molecule N),hy⟩
    · rintro ⟨j,hj⟩
      by_cases h : j ≤ Fintype.card (Molecule N)
      · exact revClosureAt_mono_stage _ _ h hj
      · have hjj : j = Fintype.card (Molecule N)+(j-Fintype.card (Molecule N)) := by omega
        rw [hjj,closure_stable_after_card] at hj
        exact hj
  apply long_target_productive_history _ molLength _ S k x _ hlen
  · intro T y hy
    exact quotient_sparse_closure_length N T y (by rwa [he] at hy)
  · rwa [he]

end RAFCriticalWindowQuantitative
