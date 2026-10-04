module

public import proofs.RAFCriticalWindowQuantitative.FiniteClosure

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAF.Concrete RAF.Polymer

def settledChannels {M R : Type*} [DecidableEq M] (Q : ReversibleCRS M R)
    (S : Finset R) (C : Finset M) : Finset R :=
  S.filter (fun r => Q.lhs r ⊆ C ∧ Q.rhs r ⊆ C)

theorem settledChannels_mono {M R : Type*} [DecidableEq M] (Q : ReversibleCRS M R)
    (S : Finset R) {C D : Finset M} (h : C ⊆ D) :
    settledChannels Q S C ⊆ settledChannels Q S D := by
  intro r hr
  obtain ⟨hr,hleft,hright⟩ := Finset.mem_filter.mp hr
  exact Finset.mem_filter.mpr ⟨hr,hleft.trans h,hright.trans h⟩

theorem enabled_settled_next {M R : Type*} [DecidableEq M] (Q : ReversibleCRS M R)
    (S : Finset R) (C : Finset M) (r : R) (hr : r ∈ S)
    (hen : RevEnabledLhs Q C r ∨ RevEnabledRhs Q C r) :
    r ∈ settledChannels Q S (revClosureStep Q S C) := by
  have hold : C ⊆ revClosureStep Q S C := Finset.subset_union_left
  have hadd : (if RevEnabledLhs Q C r then Q.rhs r else ∅) ∪
      (if RevEnabledRhs Q C r then Q.lhs r else ∅) ⊆ revClosureStep Q S C := by
    intro x hx
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r,hr,hx⟩)
  apply Finset.mem_filter.mpr
  refine ⟨hr,?_⟩
  rcases hen with hL | hR
  · refine ⟨hL.trans hold,?_⟩
    intro x hx
    apply hadd
    apply Finset.mem_union_left
    simpa only [ite_eq_left hL] using hx
  · refine ⟨?_,hR.trans hold⟩
    intro x hx
    apply hadd
    apply Finset.mem_union_right
    simpa only [ite_eq_left hR] using hx

theorem growing_closure_grows_settled {M R : Type*} [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) (C : Finset M)
    (hg : revClosureStep Q S C ≠ C) :
    (settledChannels Q S C).card < (settledChannels Q S (revClosureStep Q S C)).card := by
  classical
  have hold : C ⊆ revClosureStep Q S C := Finset.subset_union_left
  have hn : ¬ revClosureStep Q S C ⊆ C := fun hh => hg (Finset.Subset.antisymm hh hold)
  obtain ⟨x,hx,hnot⟩ := Finset.not_subset.mp hn
  have hxnew : x ∈ S.biUnion (fun r =>
      (if RevEnabledLhs Q C r then Q.rhs r else ∅) ∪
      (if RevEnabledRhs Q C r then Q.lhs r else ∅)) :=
    (Finset.mem_union.mp hx).resolve_left hnot
  obtain ⟨r,hr,hxr⟩ := Finset.mem_biUnion.mp hxnew
  have hactive : RevEnabledLhs Q C r ∨ RevEnabledRhs Q C r := by
    by_contra hh
    push Not at hh
    simp [hh.1,hh.2] at hxr
  have hsettled := enabled_settled_next Q S C r hr hactive
  have hnotsettled : r ∉ settledChannels Q S C := by
    intro hs
    obtain ⟨_,hleft,hright⟩ := Finset.mem_filter.mp hs
    rcases Finset.mem_union.mp hxr with hxL | hxR
    · by_cases hL : RevEnabledLhs Q C r
      · exact hnot (hright (by simpa only [ite_eq_left hL] using hxL))
      · simp [hL] at hxL
    · by_cases hR : RevEnabledRhs Q C r
      · exact hnot (hleft (by simpa only [ite_eq_left hR] using hxR))
      · simp [hR] at hxR
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨settledChannels_mono Q S hold,?_⟩
  intro he
  exact hnotsettled (he.symm ▸ hsettled)

theorem settled_growth_or_stable {M R : Type*} [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) (k : ℕ) :
    k ≤ (settledChannels Q S (revClosureAt Q S k)).card ∨
      revClosureAt Q S (k+1) = revClosureAt Q S k := by
  induction k with
  | zero => exact Or.inl (Nat.zero_le _)
  | succ k ih =>
    by_cases he : revClosureAt Q S (k+1) = revClosureAt Q S k
    · right
      change revClosureStep Q S (revClosureAt Q S (k+1)) = _
      rw [he]
      exact he
    · have hk := ih.resolve_right he
      exact Or.inl (Nat.succ_le_of_lt (lt_of_le_of_lt hk (growing_closure_grows_settled Q S _ he)))

/-- Each nonstationary round finishes at least one new channel. -/
theorem closure_stable_at_channel_count {M R : Type*} [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) :
    revClosureAt Q S (S.card+1) = revClosureAt Q S S.card := by
  rcases settled_growth_or_stable Q S S.card with hg | he
  · by_contra hn
    have hh := growing_closure_grows_settled Q S (revClosureAt Q S S.card) hn
    have hbound : (settledChannels Q S (revClosureStep Q S (revClosureAt Q S S.card))).card ≤ S.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    omega
  · exact he

theorem closure_stable_after_channel_count {M R : Type*} [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) (j : ℕ) :
    revClosureAt Q S (S.card+j) = revClosureAt Q S S.card := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.add_succ,revClosureAt,ih]
    exact closure_stable_at_channel_count Q S

theorem temporaryClosure_eq_channel_iteration (N L : ℕ) (S : Finset (Reaction N)) :
    temporaryReactionClosure L S = revClosureAt (binaryPolymerCRS N L) S S.card := by
  classical
  ext x
  rw [mem_temporaryReactionClosure]
  constructor
  · rintro ⟨k,hk⟩
    by_cases h : k ≤ S.card
    · exact revClosureAt_mono_stage _ _ h hk
    · have he : k = S.card+(k-S.card) := by omega
      rw [he,closure_stable_after_channel_count] at hk
      exact hk
  · intro hx
    exact ⟨S.card,hx⟩

theorem finite_iteration_length (N : ℕ) (S : Finset (Reaction N)) (k : ℕ)
    (x : Molecule N) (hx : x ∈ revClosureAt (binaryPolymerCRS N 2) S k) :
    molLength x ≤ 2^(k+1) := by
  classical
  induction k generalizing x with
  | zero =>
    exact (Finset.mem_filter.mp hx).2
  | succ k ih =>
    have hinc : 2^(k+1) ≤ 2^(k+1+1) := by
      rw [pow_succ]
      omega
    change x ∈ revClosureStep (binaryPolymerCRS N 2) S
      (revClosureAt (binaryPolymerCRS N 2) S k) at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (ih x hx).trans hinc
    · obtain ⟨r,_,hx⟩ := Finset.mem_biUnion.mp hx
      have hlen : molLength (reactionLeft r)+molLength (reactionRight r) =
          molLength (reactionProduct r) := by
        simp only [molLength_reactionLeft,molLength_reactionRight,molLength_reactionProduct,reaction_length_add]
      rcases Finset.mem_union.mp hx with hx | hx
      · by_cases hen : RevEnabledLhs (binaryPolymerCRS N 2)
            (revClosureAt (binaryPolymerCRS N 2) S k) r
        · rw [ite_eq_left hen] at hx
          have he : x = reactionProduct r := Finset.mem_singleton.mp hx
          have hl := ih (reactionLeft r) (hen (by simp [binaryPolymerCRS]))
          have hr := ih (reactionRight r) (hen (by simp [binaryPolymerCRS]))
          rw [he,pow_succ]
          omega
        · simp [hen] at hx
      · by_cases hen : RevEnabledRhs (binaryPolymerCRS N 2)
            (revClosureAt (binaryPolymerCRS N 2) S k) r
        · rw [ite_eq_left hen] at hx
          have hp := ih (reactionProduct r) (hen (by simp [binaryPolymerCRS]))
          have hx' : x = reactionLeft r ∨ x = reactionRight r := by
            simpa only [binaryPolymerCRS,Finset.mem_insert,Finset.mem_singleton] using hx
          rcases hx' with rfl | rfl <;> omega
        · simp [hen] at hx

/-- A sparse set of open channels cannot generate an arbitrarily long molecule. -/
theorem sparse_closure_length (N : ℕ) (S : Finset (Reaction N))
    (x : Molecule N) (hx : x ∈ temporaryReactionClosure 2 S) :
    molLength x ≤ 2^(S.card+1) := by
  rw [temporaryClosure_eq_channel_iteration] at hx
  exact finite_iteration_length N S S.card x hx

end RAFCriticalWindowQuantitative
