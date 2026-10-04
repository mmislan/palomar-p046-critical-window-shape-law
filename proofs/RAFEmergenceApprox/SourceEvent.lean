module

public import proofs.HordijkSteelThreshold.TerminalReactionClosure
public import proofs.HordijkSteelThreshold.PeelingStabilization
public import proofs.HordijkSteelThreshold.ScalarHistoryLaw

@[expose] public section

namespace RAFEmergenceApprox
open Classical RAF RAF.Polymer RAF.Concrete HordijkSteelThreshold

/-- Extraction needs nonemptiness, not growth beyond food. -/
theorem usable_isRAF {N L : ℕ} (A : Finset (Reaction N))
    (Cat : Catalysis (Molecule N) (Reaction N))
    (hcat : ∀ r ∈ A, ∃ x ∈ temporaryReactionClosure L A, Cat x r)
    (hne : (usableClosureReactions L A).Nonempty) :
    IsRevRAF (binaryPolymerCRS N L) Cat (usableClosureReactions L A) := by
  refine ⟨hne, ?_, ?_⟩
  · intro r hr
    have hh := (Finset.mem_filter.mp hr).2
    have he := usableClosureReactions_closure (L := L) A
    have hl : reactionLeft r ∈ temporaryReactionClosure L (usableClosureReactions L A) := by
      rw [he]; exact hh.1
    have hr' : reactionRight r ∈ temporaryReactionClosure L (usableClosureReactions L A) := by
      rw [he]; exact hh.2.1
    have hp : reactionProduct r ∈ temporaryReactionClosure L (usableClosureReactions L A) := by
      rw [he]; exact hh.2.2
    obtain ⟨kl,hkl⟩ := (mem_temporaryReactionClosure _ _).mp hl
    obtain ⟨kr,hkr⟩ := (mem_temporaryReactionClosure _ _).mp hr'
    obtain ⟨kp,hkp⟩ := (mem_temporaryReactionClosure _ _).mp hp
    have hlk := revClosureAt_mono_stage _ _ (Nat.le_max_left kl (max kr kp)) hkl
    have hrk := revClosureAt_mono_stage _ _
      ((Nat.le_max_left kr kp).trans (Nat.le_max_right kl (max kr kp))) hkr
    have hpk := revClosureAt_mono_stage _ _
      ((Nat.le_max_right kr kp).trans (Nat.le_max_right kl (max kr kp))) hkp
    refine ⟨max kl (max kr kp), ?_⟩
    intro y hy
    have hmem : y = reactionLeft r ∨ y = reactionRight r ∨ y = reactionProduct r := by
      simpa [binaryPolymerCRS] using hy
    rcases hmem with rfl | rfl | rfl
    · exact hlk
    · exact hrk
    · exact hpk
  · intro r hr
    obtain ⟨x,hx,hxr⟩ := hcat r (Finset.mem_filter.mp hr).1
    rw [← usableClosureReactions_closure A] at hx
    obtain ⟨k,hk⟩ := (mem_temporaryReactionClosure _ _).mp hx
    exact ⟨x,k,hk,hxr⟩

theorem raf_subset_peeling {n L : ℕ} (ω : AmbientCoord n → Prop)
    {S : Finset (Reaction n)}
    (hS : IsRevRAF (binaryPolymerCRS n L) (fun x r => ω (x,r)) S) (t : ℕ) :
    S ⊆ peelingActiveAt (catalystActive ω) (temporaryReactionClosure L) t := by
  induction t with
  | zero =>
    intro r hr
    obtain ⟨x,k,_,hx⟩ := hS.2.2 r hr
    exact (mem_catalystActive _ _ _).mpr ⟨x,Finset.mem_univ _,hx⟩
  | succ t ih =>
    intro r hr
    obtain ⟨x,k,hx,hcat⟩ := hS.2.2 r hr
    apply (mem_catalystActive _ _ _).mpr
    exact ⟨x, temporaryReactionClosure_mono ih
      ((mem_temporaryReactionClosure S x).mpr ⟨k,hx⟩),hcat⟩

/-- Exact terminal test for the literal split-position reversible source,
with arbitrary food horizon and no nonfood-growth premise. -/
theorem source_terminal_iff {n L : ℕ} (ω : AmbientCoord n → Prop) :
    (∃ S : Finset (Reaction n),
      IsRevRAF (binaryPolymerCRS n L) (fun x r => ω (x,r)) S) ↔
    (usableClosureReactions L (peelingActiveAt (catalystActive ω)
      (temporaryReactionClosure L) (Fintype.card (Reaction n)))).Nonempty := by
  let A := peelingActiveAt (catalystActive ω) (temporaryReactionClosure L)
    (Fintype.card (Reaction n))
  constructor
  · rintro ⟨S,hS⟩
    have hsub : S ⊆ A := raf_subset_peeling ω hS _
    obtain ⟨r,hr⟩ := hS.1
    obtain ⟨k,hk⟩ := hS.2.1 r hr
    have hend : ∀ x ∈ (binaryPolymerCRS n L).lhs r ∪
        (binaryPolymerCRS n L).rhs r, x ∈ temporaryReactionClosure L A := by
      intro x hx
      exact temporaryReactionClosure_mono hsub
        ((mem_temporaryReactionClosure S x).mpr ⟨k,hk hx⟩)
    refine ⟨r,Finset.mem_filter.mpr ⟨hsub hr, ?_, ?_, ?_⟩⟩
    · exact hend _ (by simp [binaryPolymerCRS])
    · exact hend _ (by simp [binaryPolymerCRS])
    · exact hend _ (by simp [binaryPolymerCRS])
  · intro hne
    have hs : catalystActive ω (temporaryReactionClosure L A) = A :=
      peelingActiveAt_stable_card _ _ (catalystActive_mono ω)
        (fun _ _ h => temporaryReactionClosure_mono h)
    refine ⟨usableClosureReactions L A, usable_isRAF A _ ?_ hne⟩
    intro r hr
    apply (mem_catalystActive _ _ _).mp
    rwa [hs]

end RAFEmergenceApprox
