import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

open Set MeasureTheory

namespace CubeSqrtProbability

def facePass (strict : Bool) (y c : ℝ) : Prop :=
  if strict then y < c else y ≤ c

def faceEvent {Ω ι : Type*} (Y : Ω → ι → ℝ) (strict : ι → Bool)
    (c : ι → ℝ) (t : ℝ) : Set Ω :=
  {w | ∀ i, facePass (strict i) (Y w i) (c i + t)}

def badFaceNoise {Ω ι : Type*} (N : Ω → ι → ℝ) (η : ℝ) : Set Ω :=
  {w | ∃ i, η < |N w i|}

theorem face_perturb_upper {Ω ι : Type*} (Y N : Ω → ι → ℝ)
    (strict : ι → Bool) (c : ι → ℝ) (t η : ℝ) :
    faceEvent Y strict c t ⊆
      faceEvent (fun w i ↦ Y w i + N w i) strict c (t+η) ∪ badFaceNoise N η := by
  intro w hw
  by_cases hb : w ∈ badFaceNoise N η
  · exact Or.inr hb
  left
  intro i
  have ha : |N w i| ≤ η := le_of_not_gt (fun hh ↦ hb ⟨i,hh⟩)
  have hn : N w i ≤ η := (le_abs_self _).trans ha
  have hf := hw i
  cases hs : strict i <;> simp [facePass,hs] at hf ⊢ <;> linarith

theorem face_perturb_lower {Ω ι : Type*} (Y N : Ω → ι → ℝ)
    (strict : ι → Bool) (c : ι → ℝ) (t η : ℝ) :
    faceEvent (fun w i ↦ Y w i + N w i) strict c t ⊆
      faceEvent Y strict c (t+η) ∪ badFaceNoise N η := by
  intro w hw
  by_cases hb : w ∈ badFaceNoise N η
  · exact Or.inr hb
  left
  intro i
  have ha : |N w i| ≤ η := le_of_not_gt (fun hh ↦ hb ⟨i,hh⟩)
  have hn := (abs_le.mp ha).1
  have hf := hw i
  cases hs : strict i <;> simp [facePass,hs] at hf ⊢ <;> linarith

theorem polyhedral_difference_le {Ω Ω' ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ω') [IsProbabilityMeasure ν]
    (Y N : Ω → ι → ℝ) (G M : Ω' → ι → ℝ)
    (strict : ι → Bool) (c : ι → ℝ) (η δ β α : ℝ)
    (hμ : μ.real (badFaceNoise N η) ≤ β)
    (hν : ν.real (badFaceNoise M η) ≤ β)
    (hc : ∀ t, |μ.real (faceEvent (fun w i ↦ Y w i+N w i) strict c t) -
        ν.real (faceEvent (fun w i ↦ G w i+M w i) strict c t)| ≤ δ)
    (hUpper : ν.real (faceEvent G strict c (2*η)) -
      ν.real (faceEvent G strict c 0) ≤ α)
    (hLower : ν.real (faceEvent G strict c 0) -
      ν.real (faceEvent G strict c (-2*η)) ≤ α) :
    |μ.real (faceEvent Y strict c 0) - ν.real (faceEvent G strict c 0)| ≤
      δ + 2*β + α := by
  let Yp := fun w i ↦ Y w i + N w i
  let Gp := fun w i ↦ G w i + M w i
  have y0 : μ.real (faceEvent Y strict c 0) ≤ μ.real (faceEvent Yp strict c η) + β := by
    have h' := (measureReal_mono (μ := μ) (face_perturb_upper Y N strict c 0 η)).trans
      ((measureReal_union_le _ _).trans (add_le_add (le_refl _) hμ))
    simpa [Yp] using h'
  have ym : μ.real (faceEvent Yp strict c (-η)) ≤ μ.real (faceEvent Y strict c 0) + β := by
    have h' := (measureReal_mono (μ := μ) (face_perturb_lower Y N strict c (-η) η)).trans
      ((measureReal_union_le _ _).trans (add_le_add (le_refl _) hμ))
    simpa [Yp] using h'
  have gp : ν.real (faceEvent Gp strict c η) ≤ ν.real (faceEvent G strict c (2*η)) + β := by
    have h' := (measureReal_mono (μ := ν) (face_perturb_lower G M strict c η η)).trans
      ((measureReal_union_le _ _).trans (add_le_add (le_refl _) hν))
    simpa [Gp,two_mul] using h'
  have gm : ν.real (faceEvent G strict c (-2*η)) ≤ ν.real (faceEvent Gp strict c (-η)) + β := by
    have ht : -2*η+η = -η := by ring
    have h' := (measureReal_mono (μ := ν) (face_perturb_upper G M strict c (-2*η) η)).trans
      ((measureReal_union_le _ _).trans (add_le_add (le_refl _) hν))
    rw [ht] at h'
    exact h'
  have hp := (abs_le.mp (hc η)).2
  have hm := (abs_le.mp (hc (-η))).1
  exact abs_le.mpr ⟨by dsimp [Yp,Gp] at *; linarith, by dsimp [Yp,Gp] at *; linarith⟩

end CubeSqrtProbability
#print axioms CubeSqrtProbability.polyhedral_difference_le
