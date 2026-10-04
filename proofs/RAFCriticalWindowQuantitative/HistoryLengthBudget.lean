module

public import proofs.RAFCriticalWindowQuantitative.ProductiveHistory

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAF.Concrete RAF.Polymer

theorem settled_fixed {M R : Type*} [DecidableEq M] (Q : ReversibleCRS M R)
    (S : Finset R) (C : Finset M) (hs : ∀ r ∈ S, Q.lhs r ⊆ C ∧ Q.rhs r ⊆ C) :
    revClosureStep Q S C = C := by
  apply Finset.Subset.antisymm _ Finset.subset_union_left
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact hx
  · obtain ⟨r,hr,hx⟩ := Finset.mem_biUnion.mp hx
    have hh := hs r hr
    rcases Finset.mem_union.mp hx with hx | hx
    · split_ifs at hx with h
      · exact hh.2 hx
      · exact False.elim (Finset.notMem_empty x hx)
    · split_ifs at hx with h
      · exact hh.1 hx
      · exact False.elim (Finset.notMem_empty x hx)

theorem productive_enabled {M R : Type*} [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (C : Finset M) (r : R)
    (hg : revClosureStep Q {r} C ≠ C) : RevEnabledLhs Q C r ∨ RevEnabledRhs Q C r := by
  by_contra h
  push Not at h
  apply hg
  simp [revClosureStep,h.1,h.2]

theorem fullClosure_minimal {M R : Type*} [Fintype M] [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) (C : Finset M)
    (hf : Q.food ⊆ C) (hc : revClosureStep Q S C = C) : fullClosure Q S ⊆ C := by
  have hall : ∀ k, revClosureAt Q S k ⊆ C := by
    intro k
    induction k with
    | zero => exact hf
    | succ k ih =>
      exact (revClosureStep_mono Q Finset.Subset.rfl ih).trans (Finset.subset_of_eq hc)
  exact hall _

/-- The history invariant prevents a hidden cascade after insertion. -/
theorem settled_insert_closure {M R : Type*} [Fintype M] [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (T : Finset R) (r : R)
    (hs : ∀ t ∈ T, Q.lhs t ⊆ fullClosure Q T ∧ Q.rhs t ⊆ fullClosure Q T)
    (hg : revClosureStep Q {r} (fullClosure Q T) ≠ fullClosure Q T) :
    fullClosure Q (insert r T) = revClosureStep Q {r} (fullClosure Q T) := by
  let C := fullClosure Q T
  let D := revClosureStep Q {r} C
  have hCD : C ⊆ D := Finset.subset_union_left
  have hrD : Q.lhs r ⊆ D ∧ Q.rhs r ⊆ D := by
    exact (Finset.mem_filter.mp (enabled_settled_next Q {r} C r (Finset.mem_singleton_self _)
      (productive_enabled Q C r hg))).2
  have hsettled : ∀ t ∈ insert r T, Q.lhs t ⊆ D ∧ Q.rhs t ⊆ D := by
    intro t ht
    rcases Finset.mem_insert.mp ht with he | ht
    · subst t
      exact hrD
    · exact ⟨(hs t ht).1.trans hCD,(hs t ht).2.trans hCD⟩
  apply Finset.Subset.antisymm
  · apply fullClosure_minimal Q (insert r T) D
    · exact (revClosureAt_mono_stage Q T (Nat.zero_le _)).trans hCD
    · exact settled_fixed Q _ D hsettled
  · have hC : C ⊆ fullClosure Q (insert r T) :=
      revClosureAt_mono_reactions Q (Finset.subset_insert _ _) _
    have hstep := revClosureStep_mono Q (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self r T)) hC
    exact hstep.trans (Finset.subset_of_eq (closure_stable_at_card Q (insert r T)))

theorem productive_history_settled {M R : Type*} [Fintype M] [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) {k T} (h : ProductiveHistory Q S k T) :
    ∀ r ∈ T, Q.lhs r ⊆ fullClosure Q T ∧ Q.rhs r ⊆ fullClosure Q T := by
  induction h with
  | nil => simp
  | @step k T r h hr hrT hg ih =>
    rw [settled_insert_closure Q T r ih hg]
    intro t ht
    rcases Finset.mem_insert.mp ht with he | ht
    · subst t
      exact (Finset.mem_filter.mp (enabled_settled_next Q {r} (fullClosure Q T) r
        (Finset.mem_singleton_self _) (productive_enabled Q _ r hg))).2
    · exact ⟨(ih t ht).1.trans Finset.subset_union_left,(ih t ht).2.trans Finset.subset_union_left⟩

def historyBudget (j : ℕ) : ℕ := (6+2*j)^2+4*2^j-j
def historyCoefficient (g : ℕ) : ℕ → ℕ
  | 0 => 1
  | r+1 => if r=0 then g else historyCoefficient g r * historyBudget r

theorem quadratic_history_envelope (j : ℕ) (hj : 1 ≤ j) : (6+2*j)^2 ≤ 32*2^j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have hq : (6+2*(j+1))^2 ≤ 2*(6+2*j)^2 := by nlinarith
    rw [show 2^(j+1)=2^j*2 from pow_succ 2 j]
    nlinarith

theorem historyBudget_envelope (j : ℕ) (hj : 1 ≤ j) : historyBudget j ≤ 36*2^j := by
  have h := quadratic_history_envelope j hj
  unfold historyBudget
  omega

end RAFCriticalWindowQuantitative
