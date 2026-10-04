module

public import proofs.HordijkSteelThreshold.RecordTargetTrial

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold

/-- The first record above a completed prefix occurs by twice that prefix. -/
theorem generated_or_bounded_record {L B : ℕ} (hLB : L ≤ B)
    {field : InfiniteSplitEnvironment} {w : List Bool}
    (h : InfiniteReversibleGenerated L field w) :
    FiniteReversibleGenerated B L field w ∨
      ∃ v, B < v.length ∧ v.length ≤ 2*B ∧
        FiniteReversibleGenerated v.length L field v := by
  induction h with
  | food hn hL => exact Or.inl (.food hn hL (hL.trans hLB))
  | @ligate u v _ _ ho ihu ihv =>
    rcases ihu with hu | he
    · rcases ihv with hv | he
      · by_cases hlen : (u++v).length ≤ B
        · exact Or.inl (.ligate hu hv ho hlen)
        · have hb : B ≤ (u++v).length := by omega
          have huB := finiteReversibleGenerated_length_le hu
          have hvB := finiteReversibleGenerated_length_le hv
          refine Or.inr ⟨u++v, by omega, ?_, .ligate
            (finiteReversibleGenerated_mono_cap hb hu)
            (finiteReversibleGenerated_mono_cap hb hv) ho le_rfl⟩
          simp only [List.length_append]
          omega
      · exact Or.inr he
    · exact Or.inr he
  | left hu hv _ ho ih =>
    rcases ih with hp | he
    · exact Or.inl (.left hu hv hp ho)
    · exact Or.inr he
  | right hu hv _ ho ih =>
    rcases ih with hp | he
    · exact Or.inl (.right hu hv hp ho)
    · exact Or.inr he

theorem escape_has_bounded_record {L B : ℕ} (hLB : L ≤ B)
    {field : InfiniteSplitEnvironment}
    (h : ∃ w, B < w.length ∧ InfiniteReversibleGenerated L field w) :
    ∃ v, B < v.length ∧ v.length ≤ 2*B ∧
      FiniteReversibleGenerated v.length L field v := by
  obtain ⟨w,hw,hg⟩ := h
  rcases generated_or_bounded_record hLB hg with hf | he
  · have hl := finiteReversibleGenerated_length_le hf
    omega
  · exact he

/-- A subtraction-free form of the deterministic exposure budget. -/
theorem exposure_budget (ell : ℕ) (D : ℕ → ℕ) (h0 : D 0 ≤ 2)
    (hs : ∀ j, D (j+1) ≤ 2*D j+ell) (j : ℕ) :
    D j+ell ≤ 2^j*(2+ell) := by
  induction j with
  | zero => simpa using Nat.add_le_add_right h0 ell
  | succ j ih =>
    have h := hs j
    rw [pow_succ]
    nlinarith

end RAFCriticalWindowQuantitative
