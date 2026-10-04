module

public import proofs.RAFCriticalWindowQuantitative.SparseClosure
public import proofs.RAFReactionQuotient.History

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 100000

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient RAF.Concrete RAF.Polymer OverlapCorrectedRAF.Source

theorem quotientClosure_eq_channel_iteration (N L : ℕ) (S : Finset (RepositoryChannel N)) :
    quotientClosure N L S = revClosureAt (repositoryCRS N L) S S.card := by
  classical
  ext x
  rw [mem_quotientClosure]
  constructor
  · rintro ⟨k,hk⟩
    by_cases h : k ≤ S.card
    · exact revClosureAt_mono_stage _ _ h hk
    · have he : k = S.card+(k-S.card) := by omega
      rw [he,closure_stable_after_channel_count] at hk
      exact hk
  · intro hx
    exact ⟨S.card,hx⟩

theorem quotient_iteration_length (N : ℕ) (S : Finset (RepositoryChannel N)) (k : ℕ)
    (x : Molecule N) (hx : x ∈ revClosureAt (repositoryCRS N 2) S k) :
    molLength x ≤ 2^(k+1) := by
  classical
  induction k generalizing x with
  | zero =>
    exact (Finset.mem_filter.mp hx).2
  | succ k ih =>
    have hinc : 2^(k+1) ≤ 2^(k+1+1) := by
      rw [pow_succ]
      omega
    change x ∈ revClosureStep (repositoryCRS N 2) S
      (revClosureAt (repositoryCRS N 2) S k) at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (ih x hx).trans hinc
    · obtain ⟨r,_,hx⟩ := Finset.mem_biUnion.mp hx
      have hlen : molLength (r.val.1)+molLength (r.val.2) =
          molLength (concatMolecule r.val.1 r.val.2 r.property.1) := by
        simp [concatMolecule]
      rcases Finset.mem_union.mp hx with hx | hx
      · by_cases hen : RevEnabledLhs (repositoryCRS N 2)
            (revClosureAt (repositoryCRS N 2) S k) r
        · rw [ite_eq_left hen] at hx
          have he : x = concatMolecule r.val.1 r.val.2 r.property.1 := Finset.mem_singleton.mp hx
          have hl := ih (r.val.1) (hen (by simp [repositoryCRS]))
          have hr := ih (r.val.2) (hen (by simp [repositoryCRS]))
          rw [he,pow_succ]
          omega
        · simp [hen] at hx
      · by_cases hen : RevEnabledRhs (repositoryCRS N 2)
            (revClosureAt (repositoryCRS N 2) S k) r
        · rw [ite_eq_left hen] at hx
          have hp := ih (concatMolecule r.val.1 r.val.2 r.property.1) (hen (by simp [repositoryCRS]))
          have hx' : x = r.val.1 ∨ x = r.val.2 := by
            simpa only [repositoryCRS,Finset.mem_insert,Finset.mem_singleton] using hx
          rcases hx' with rfl | rfl <;> omega
        · simp [hen] at hx

/-- A sparse set of open channels cannot generate an arbitrarily long molecule. -/
theorem quotient_sparse_closure_length (N : ℕ) (S : Finset (RepositoryChannel N))
    (x : Molecule N) (hx : x ∈ quotientClosure N 2 S) :
    molLength x ≤ 2^(S.card+1) := by
  rw [quotientClosure_eq_channel_iteration] at hx
  exact quotient_iteration_length N S S.card x hx

end RAFCriticalWindowQuantitative
