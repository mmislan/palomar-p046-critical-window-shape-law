module

public import proofs.HordijkSteelThreshold.PeelingStabilization

@[expose] public section

namespace RAFEmergenceApprox
open Classical HordijkSteelThreshold

def thresholdOpen {R : Type*} [Fintype R] (T : R → ℕ) (k : ℕ) : Finset R :=
  Finset.univ.filter (fun r => T r ≤ k)

theorem thresholdOpen_mono {R : Type*} [Fintype R] (T : R → ℕ) :
    Monotone (thresholdOpen T) := by
  intro a b hab r hr
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    ((Finset.mem_filter.mp hr).2).trans hab⟩

theorem scalar_barrier_subset {X R : Type*} [Fintype X] [Fintype R]
    (O : ℕ → Finset R) (closure : Finset R → Finset X)
    (hO : Monotone O) (hc : Monotone closure) (k : ℕ)
    (hk : k ≤ Fintype.card X) (hkg : k ≤ (closure (O k)).card) (t : ℕ) :
    O k ⊆ peelingActiveAt (fun C : Finset X => O C.card) closure t := by
  induction t with
  | zero => simpa [peelingActiveAt] using hO hk
  | succ t ih => exact hO (hkg.trans (Finset.card_le_card (hc ih)))

/-- Exact scalar terminal criterion, for any monotone finite closure.
The growth premise is subsequently proved for the literal source closure. -/
theorem scalar_terminal_criterion {X R : Type*} [Fintype X] [Fintype R]
    (O : ℕ → Finset R) (closure : Finset R → Finset X)
    (U : Finset R → Prop) (f : ℕ)
    (hO : Monotone O) (hc : Monotone closure) (hU : Monotone U)
    (hfloor : ∀ A, f ≤ (closure A).card)
    (hgrowth : ∀ A, f < (closure A).card → U A) :
    U (peelingActiveAt (fun C : Finset X => O C.card) closure (Fintype.card R)) ↔
      U (O f) ∨ ∃ k, f < k ∧ k ≤ Fintype.card X ∧ k ≤ (closure (O k)).card := by
  let A := peelingActiveAt (fun C : Finset X => O C.card) closure (Fintype.card R)
  have hs : O (closure A).card = A := peelingActiveAt_stable_card _ _
    (fun _ _ h => hO (Finset.card_le_card h)) hc
  constructor
  · intro h
    by_cases he : (closure A).card = f
    · left
      rw [he] at hs
      rwa [hs]
    · right
      refine ⟨(closure A).card, ?_, Finset.card_le_univ _, ?_⟩
      · have := hfloor A; omega
      · rw [hs]
  · rintro (h | ⟨k,hfk,hk,hkg⟩)
    · apply hU _ h
      change O f ⊆ A
      rw [← hs]
      exact hO (hfloor A)
    · apply hU (scalar_barrier_subset O closure hO hc k hk hkg _)
      exact hgrowth _ (hfk.trans_le hkg)

/-- Every nonfood barrier can be tested at its last installed threshold;
if none exceeds food, the food test already succeeds. -/
theorem threshold_batches_suffice {R : Type*} [Fintype R]
    (T : R → ℕ) (g : Finset R → ℕ) (U : Finset R → Prop) (f M : ℕ)
    (hgrowth : ∀ A, f < g A → U A) :
    (U (thresholdOpen T f) ∨
      ∃ k, f < k ∧ k ≤ M ∧ k ≤ g (thresholdOpen T k)) ↔
    (U (thresholdOpen T f) ∨
      ∃ r, f < T r ∧ T r ≤ M ∧ T r ≤ g (thresholdOpen T (T r))) := by
  constructor
  · rintro (h | ⟨k,hfk,hk,hg⟩)
    · exact Or.inl h
    · let A := thresholdOpen T k
      let t := A.sup T
      have ht : t ≤ k := Finset.sup_le (fun r hr => (Finset.mem_filter.mp hr).2)
      have he : thresholdOpen T t = A := by
        apply Finset.Subset.antisymm (thresholdOpen_mono T ht)
        intro r hr
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.le_sup hr⟩
      by_cases htf : t ≤ f
      · left
        have haf : A = thresholdOpen T f := by
          apply Finset.Subset.antisymm
          · rw [← he]; exact thresholdOpen_mono T htf
          · exact thresholdOpen_mono T (by omega)
        rw [← haf]
        exact hgrowth A (hfk.trans_le hg)
      · right
        have hne : A.Nonempty := by
          by_contra hn
          have hz : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
          simp [t,hz] at htf
        obtain ⟨r,hr,hrt⟩ := Finset.exists_mem_eq_sup A hne T
        refine ⟨r, ?_, ?_, ?_⟩
        · omega
        · omega
        · have her : thresholdOpen T (T r) = A := by rw [← hrt]; exact he
          rw [her]
          change k ≤ g A at hg
          omega
  · rintro (h | ⟨r,hf,hm,hg⟩)
    · exact Or.inl h
    · exact Or.inr ⟨T r,hf,hm,hg⟩

end RAFEmergenceApprox
