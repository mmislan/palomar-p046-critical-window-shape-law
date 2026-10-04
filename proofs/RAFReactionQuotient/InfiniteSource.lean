module

public import proofs.HordijkSteelThreshold.RecordTargetTrial
public import proofs.HordijkSteelThreshold.StaticSurvivalMonotonicity
public import proofs.HordijkSteelThreshold.SplitPrefixIndependence

@[expose] public section

namespace RAFReactionQuotient
open Classical MeasureTheory unitInterval HordijkSteelThreshold

/-- Canonicalize a valid split only when the factors commute and the right
factor is shorter. Equal-length commuting factors are identical, so there is
no separate tie to collapse. Invalid coordinates are harmless unused marks. -/
def canonicalIndex (z : List Bool × ℕ) : List Bool × ℕ :=
  if 0 < z.2 ∧ z.2 < z.1.length ∧ z.1.length-z.2 < z.2 ∧
      z.1.take z.2 ++ z.1.drop z.2 = z.1.drop z.2 ++ z.1.take z.2 then
    (z.1,z.1.length-z.2)
  else z

@[simp] theorem canonicalIndex_product (z : List Bool × ℕ) :
    (canonicalIndex z).1 = z.1 := by unfold canonicalIndex; split <;> rfl

theorem canonicalIndex_prefix {B : ℕ} {z : List Bool × ℕ}
    (hz : z ∈ splitPrefixCoordinates B) : canonicalIndex z ∈ splitPrefixCoordinates B := by
  have hz' := (mem_splitPrefixCoordinates B z).mp hz
  apply (mem_splitPrefixCoordinates B _).mpr
  unfold canonicalIndex
  split
  · dsimp
    exact ⟨hz'.1,(Nat.sub_le _ _).trans hz'.1⟩
  · exact hz'

def quotientField (ω : SplitField) : InfiniteSplitEnvironment :=
  fun w k => ω (canonicalIndex (w,k))

theorem quotientField_measurable : Measurable quotientField := by
  apply Measurable.of_eval
  intro w
  apply Measurable.of_eval
  intro k
  exact measurable_pi_apply _

/-- Infinite reversible quotient survival, realized by iid marks on canonical
coordinates. Noncanonical and invalid latent coordinates do not affect it. -/
noncomputable def quotientSurvival (a : I) : ENNReal :=
  infiniteSplitPi a {ω | ReversibleUnbounded 2 (quotientField ω)}

theorem quotient_own_cap_record {ω : SplitField}
    (h : ReversibleUnbounded 2 (quotientField ω)) (B : ℕ) :
    ∃ w, B < w.length ∧ FiniteReversibleGenerated w.length 2 (quotientField ω) w :=
  unbounded_record_words h B

/-- Project the literal target trial to distinct canonical coordinates.
Product-length preservation keeps every coordinate outside the record prefix. -/
theorem quotient_record_support (w v : List Bool) (hw : 0 < w.length) (hv : 0 < v.length) :
    ∃ T : Finset (List Bool × ℕ), T.card ≤ v.length+1 ∧
      Disjoint (splitPrefixCoordinates w.length) T ∧
      ∀ ω : SplitField, FiniteReversibleGenerated w.length 2 (quotientField ω) w →
        (∀ z ∈ T, ω z) → InfiniteReversibleGenerated 2 (quotientField ω) v := by
  let N := w.length+v.length
  obtain ⟨S,hsize,hband,hgen⟩ := target_trial_support (N := N) w v hw hv le_rfl
  let T := S.image (fun r => canonicalIndex (literalSplitCoordinate r))
  refine ⟨T,(Finset.card_image_le).trans hsize,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro z hz ht
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ht
    have hl := (mem_splitPrefixCoordinates w.length _).mp hz
    rw [canonicalIndex_product] at hl
    have hb := (hband r hr).1
    change (moleculeWord (RAF.Concrete.reactionProduct r)).length ≤ w.length ∧ _ at hl
    rw [moleculeWord_length] at hl
    omega
  · intro ω hrecord hopen
    have hgN := finiteReversibleGenerated_mono_cap (show w.length ≤ N by dsimp [N]; omega) hrecord
    obtain ⟨x,hx,he⟩ := finiteReversible_to_literalClosure hgN
    have hs : S ⊆ restrictedSplitReactions N (quotientField ω) := by
      intro r hr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hopen _ (Finset.mem_image.mpr ⟨r,hr,rfl⟩)⟩
    obtain ⟨y,hy,hev⟩ := hgen (restrictedSplitReactions N (quotientField ω)) hs x hx he
    rw [← hev]
    exact finiteReversibleGenerated_to_infinite (literalClosure_to_finiteReversible _ y hy)

end RAFReactionQuotient
