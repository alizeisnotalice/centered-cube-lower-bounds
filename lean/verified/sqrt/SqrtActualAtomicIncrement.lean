import SqrtPeriodicBoxDensity

namespace CenteredCubeSqrt

open MeasureTheory
open scoped BigOperators Interval

/-- The exact centered atomic term in the paper's window density. Each
normalized box has mass one; the globally normalized density uses 1/K. -/
noncomputable def actualAtomicWindow {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (delta L x : ℝ) : ℝ :=
  (∑ j : ZMod K, ∫ y in x-L/2..x+L/2,
    periodicBoxDensity delta (paperAtomCenter f j) y) - (K:ℝ)*L

noncomputable def localLength (L0 C t : ℝ) : ℝ := L0+2*t/C

/-- This is the exact two-family expansion of the actual pulse window,
including the deterministic centering term. -/
theorem actualAtomicWindow_increment {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    {eps C T s t L0 x : ℝ}
    (he : 0 < eps) (hC : 0 < C) (hT : 0 ≤ T) (hlarge : (T+eps/2)/C < 1/4)
    (hs : -T ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    actualAtomicWindow f (eps/C) (localLength L0 C t) x -
      actualAtomicWindow f (eps/C) (localLength L0 C s) x =
    atomPulseTrain f eps (-t) (-s) C (-L0/2) x +
      atomPulseTrain f eps s t C (L0/2) x - (2*(K:ℝ)*(t-s)/C) := by
  have hδ : 0 < eps/C := div_pos he hC
  have e (j : ZMod K) :
      (∫ y in x-localLength L0 C t/2..x+localLength L0 C t/2,
        periodicBoxDensity (eps/C) (paperAtomCenter f j) y) -
      (∫ y in x-localLength L0 C s/2..x+localLength L0 C s/2,
        periodicBoxDensity (eps/C) (paperAtomCenter f j) y) =
    periodicWindowPulse eps (-t) (-s) C (x-(paperAtomCenter f j-L0/2)) +
      periodicWindowPulse eps s t C (x-(paperAtomCenter f j+L0/2)) := by
    let F := periodicBoxDensity (eps/C) (paperAtomCenter f j)
    let at' := x-L0/2+(-t)/C
    let as' := x-L0/2+(-s)/C
    let bt := x+L0/2+t/C
    let bs := x+L0/2+s/C
    have hpoints (u : ℝ) : x-localLength L0 C u/2=x-L0/2+(-u)/C ∧
        x+localLength L0 C u/2=x+L0/2+u/C := by
      unfold localLength
      constructor <;> field_simp <;> ring
    rw [(hpoints t).1,(hpoints t).2,(hpoints s).1,(hpoints s).2]
    change (∫ y in at'..bt,F y)-(∫ y in as'..bs,F y)=_
    have h1 := intervalIntegral.integral_add_adjacent_intervals
        (periodicBoxDensity_intervalIntegrable (eps/C) (paperAtomCenter f j) at' as' hδ)
        (periodicBoxDensity_intervalIntegrable (eps/C) (paperAtomCenter f j) as' bs hδ)
    have h2 := intervalIntegral.integral_add_adjacent_intervals
        (periodicBoxDensity_intervalIntegrable (eps/C) (paperAtomCenter f j) at' bs hδ)
        (periodicBoxDensity_intervalIntegrable (eps/C) (paperAtomCenter f j) bs bt hδ)
    have elower := periodicBoxDensity_small_interval (s:=-t) (t:=-s)
      (a:=paperAtomCenter f j) (c:=x-L0/2) he hC hT hlarge
      (show -T ≤ -t by linarith) (show -t ≤ -s by linarith) (show -s ≤ T by linarith)
    have eupper := periodicBoxDensity_small_interval (s:=s) (t:=t)
      (a:=paperAtomCenter f j) (c:=x+L0/2) he hC hT hlarge hs hst ht
    rw [neg_neg,neg_neg] at elower
    have er1 : x+L0/2-paperAtomCenter f j=x-(paperAtomCenter f j-L0/2) := by ring
    have er2 : x-L0/2-paperAtomCenter f j=x-(paperAtomCenter f j+L0/2) := by ring
    rw [er1] at eupper
    rw [er2] at elower
    change (∫ y in bs..bt,F y)=_ at eupper
    change (∫ y in at'..as',F y)=_ at elower
    linarith
  unfold actualAtomicWindow atomPulseTrain
  have ef : (K:ℝ)*localLength L0 C t-(K:ℝ)*localLength L0 C s = 2*(K:ℝ)*(t-s)/C := by
    unfold localLength
    field_simp; ring
  have hsum := congrArg (fun h : ZMod K → ℝ => ∑ j, h j) (funext e)
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib] at hsum
  simp_rw [show ∀ j : ZMod K, paperAtomCenter f j-L0/2=paperAtomCenter f j+(-L0/2) by
    intro j; ring] at hsum
  linarith

#print axioms actualAtomicWindow_increment

end CenteredCubeSqrt
