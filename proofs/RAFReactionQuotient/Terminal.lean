module

public import proofs.RAFReactionQuotient.FiniteApproximation
public import proofs.RAFEmergenceApprox.SourceEvent
public import proofs.RAFEmergenceApprox.ThresholdSweep
public import proofs.HordijkSteelThreshold.SourceTerminalRAF

@[expose] public section

set_option Elab.async false

namespace RAFReactionQuotient
open Classical RAF RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source HordijkSteelThreshold
open RAFEmergenceApprox.Generic

noncomputable def splitPreimage {n : ℕ} (A : Finset (RepositoryChannel n)) : Finset (Reaction n) :=
  Finset.univ.filter (fun r => splitToQuotient r ∈ A)

theorem quotientClosure_preimage {n L : ℕ} (A : Finset (RepositoryChannel n)) :
    quotientClosure n L A = temporaryReactionClosure L (splitPreimage A) := by
  have he : quotientOpen (fun j => j ∈ A) = A := by ext j; simp [quotientOpen]
  rw [← he,quotientClosure_pullback]
  congr 1
  ext r
  simp [staticOpenReactions,splitPreimage,quotientOpen]

noncomputable def quotientUsable {n : ℕ} (L : ℕ) (A : Finset (RepositoryChannel n)) :=
  (usableClosureReactions L (splitPreimage A)).image splitToQuotient

theorem quotient_usable_hasRAF {n L : ℕ} (A : Finset (RepositoryChannel n))
    (ω : RepositoryChannel n → Molecule n → Prop)
    (hcat : ∀ j ∈ A, ∃ x ∈ quotientClosure n L A, ω j x)
    (hne : (quotientUsable L A).Nonempty) :
    ∃ S, IsRevRAF (repositoryCRS n L) (fun x j => ω j x) S := by
  have hs : IsRevRAF (binaryPolymerCRS n L) (fun x r => ω (splitToQuotient r) x)
      (usableClosureReactions L (splitPreimage A)) := by
    apply RAFEmergenceApprox.usable_isRAF
    · intro r hr
      obtain ⟨x,hx,hc⟩ := hcat _ (Finset.mem_filter.mp hr).2
      exact ⟨x,(quotientClosure_preimage A) ▸ hx,hc⟩
    · exact Finset.image_nonempty.mp hne
  have he : orCatalysis splitToQuotient (fun x r => ω (splitToQuotient r) x) =
      (fun x j => ω j x) := by
    funext x j
    exact propext (quotient_mark_pullback_OR (fun j => ω j x) j)
  have h := (split_raf_iff_quotient L _).mp ⟨_,hs⟩
  rwa [he] at h

theorem quotient_raf_subset_peeling {n L : ℕ} (ω : RepositoryChannel n → Molecule n → Prop)
    {S : Finset (RepositoryChannel n)}
    (hS : IsRevRAF (repositoryCRS n L) (fun x j => ω j x) S) (t : ℕ) :
    S ⊆ peelingActiveAt (RAFEmergenceApprox.Generic.catalystActive ω) (quotientClosure n L) t := by
  induction t with
  | zero =>
    intro r hr
    obtain ⟨x,k,_,hx⟩ := hS.2.2 r hr
    exact (RAFEmergenceApprox.Generic.mem_catalystActive _ _ _).mpr ⟨x,Finset.mem_univ _,hx⟩
  | succ t ih =>
    intro r hr
    obtain ⟨x,k,hx,hcat⟩ := hS.2.2 r hr
    apply (RAFEmergenceApprox.Generic.mem_catalystActive _ _ _).mpr
    exact ⟨x,quotientClosure_mono n L ih ((mem_quotientClosure S x).mpr ⟨k,hx⟩),hcat⟩

theorem quotient_terminal_iff {n L : ℕ} (ω : RepositoryChannel n → Molecule n → Prop) :
    (∃ S, IsRevRAF (repositoryCRS n L) (fun x j => ω j x) S) ↔
    (quotientUsable L (peelingActiveAt (RAFEmergenceApprox.Generic.catalystActive ω)
      (quotientClosure n L) (Fintype.card (RepositoryChannel n)))).Nonempty := by
  let A := peelingActiveAt (RAFEmergenceApprox.Generic.catalystActive ω) (quotientClosure n L)
    (Fintype.card (RepositoryChannel n))
  constructor
  · rintro ⟨S,hS⟩
    have hs : S ⊆ A := quotient_raf_subset_peeling ω hS _
    obtain ⟨j,hj⟩ := hS.1
    obtain ⟨r,hr⟩ := splitToQuotient_surjective n j
    obtain ⟨k,hk⟩ := hS.2.1 j hj
    have hend : ∀ x ∈ (binaryPolymerCRS n L).lhs r ∪ (binaryPolymerCRS n L).rhs r,
        x ∈ temporaryReactionClosure L (splitPreimage A) := by
      intro x hx
      rw [← quotientClosure_preimage]
      apply quotientClosure_mono n L hs
      apply (mem_quotientClosure S x).mpr
      refine ⟨k,hk ?_⟩
      rwa [← splitToQuotient_lhs,← splitToQuotient_rhs,hr] at hx
    apply Finset.image_nonempty.mpr
    refine ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr ▸ hs hj⟩,?_,?_,?_⟩⟩
    · exact hend _ (by simp [binaryPolymerCRS])
    · exact hend _ (by simp [binaryPolymerCRS])
    · exact hend _ (by simp [binaryPolymerCRS])
  · intro hne
    have hs : RAFEmergenceApprox.Generic.catalystActive ω (quotientClosure n L A) = A :=
      peelingActiveAt_stable_card _ _ (RAFEmergenceApprox.Generic.catalystActive_mono ω)
        (quotientClosure_mono n L)
    apply quotient_usable_hasRAF A ω _ hne
    intro j hj
    apply (RAFEmergenceApprox.Generic.mem_catalystActive _ _ _).mp
    rwa [hs]

theorem quotient_terminal_hasRAF {n : ℕ} (ω : RepositoryChannel n → Molecule n → Prop)
    (hmass : 6 < (quotientClosure n 2 (peelingActiveAt (RAFEmergenceApprox.Generic.catalystActive ω)
      (quotientClosure n 2) (Fintype.card (RepositoryChannel n)))).card) :
    ∃ S, IsRevRAF (repositoryCRS n 2) (fun x j => ω j x) S := by
  apply (quotient_terminal_iff ω).mpr
  apply Finset.image_nonempty.mpr
  apply usableClosureReactions_nonempty
  rw [← quotientClosure_preimage]
  by_contra h
  have hs : quotientClosure n 2 (peelingActiveAt (RAFEmergenceApprox.Generic.catalystActive ω)
      (quotientClosure n 2) (Fintype.card (RepositoryChannel n))) ⊆ binaryFood n 2 := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Nat.le_of_not_gt (fun hl => h ⟨x,hx,hl⟩)⟩
  have hc := (Finset.card_le_card hs).trans (binaryFood_card_le_cutoff n 2)
  have h6 : Fintype.card (Molecule 2) = 6 := by decide
  omega

end RAFReactionQuotient
