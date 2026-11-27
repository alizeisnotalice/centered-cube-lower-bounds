import SqrtActualAtomicIncrement
import SqrtLocalAtomicCorrelations
import SqrtCenteredPulseMoments

namespace CenteredCubeSqrt

open MeasureTheory
open scoped BigOperators Interval
open Classical

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
set_option maxHeartbeats 2000000

/-- Actual difference of the length-window atom term before multiplying
by the frozen p/(K L0) coefficient. -/
noncomputable def atomicWindowIncrement {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (eps v L0 s t x : ℝ) : ℝ :=
  actualAtomicWindow f (eps/((K:ℝ)*v)) (localLength L0 ((K:ℝ)*v) t) x -
    actualAtomicWindow f (eps/((K:ℝ)*v)) (localLength L0 ((K:ℝ)*v) s) x

/-- Uniform finite-window covariance for the genuine atomic source:
all actual pair overlaps and the mean correction are included. -/
theorem actual_local_atomic_covariance {b d : ℕ} [NeZero (2^d-1)]
    [NeZero (2^b*(2^d-1))] (hd : 0 < d) (g : (LabelField d)ˣ)
    (hg : orderOf g=2^d-1) {tβ : Fin b → LabelField d}
    (htβ : LinearIndependent (ZMod 2) tβ) (hdim : 2*b ≤ d)
    (h1 : (phaseState hd g hg 1 : LabelField d) ≠ 1)
    (h1' : (phaseState hd g hg 1 : LabelField d) ∉ labelRatioSet tβ)
    {v eps T L0 s t s' t' : ℝ} {D : ℕ}
    (hv : 0 < v) (he : 0 < eps) (hT : 0 ≤ T)
    (hV : 2*T+eps < v) (hBv : ((2^b:ℕ):ℝ) ≤ 2*v) (hD : 2*(2*T+eps)+1 ≤ D)
    (hm : (T+eps/2)/((((2^d-1:ℕ):ℝ))*v) < 1/4)
    (hs : -T≤s) (hst : s≤t) (ht : t≤T)
    (hs' : -T≤s') (hst' : s'≤t') (ht' : t'≤T)
    (hSafe : ∀ k : ℤ, |(k:ℝ)-(((2^d-1:ℕ):ℝ))*L0| < 2 →
      (phaseState hd g hg (k:ZMod (2^d-1)) : LabelField d) ≠ 1 ∧
      (phaseState hd g hg (k:ZMod (2^d-1)) : LabelField d) ∉ labelRatioSet tβ) :
    let f := ordinalPhaseLabel hd g hg tβ
    let B := ((2^b:ℕ):ℝ)
    let Same := (2*(D:ℝ)+1)*(4*(2*T+eps)/B^2)*(2*T)
    let Mirror := (2*(D:ℝ)+1)*(2/B)*(2*T)
    |v*(∫ x in (0:ℝ)..1, atomicWindowIncrement f eps v L0 s t x *
      atomicWindowIncrement f eps v L0 s' t' x) - 2*pulseOverlap eps s t s' t' 0| ≤
      2*Same+2*Mirror+4*(t-s)*(t'-s')/v := by
  let f := ordinalPhaseLabel hd g hg tβ
  let K : ℕ := 2^d-1
  let C : ℝ := (K:ℝ)*v
  have hK : 0 < (K:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
  have hC : 0 < C := mul_pos hK hv
  let A := atomPulseTrain f eps (-t) (-s) C (-L0/2)
  let B := atomPulseTrain f eps s t C (L0/2)
  let A' := atomPulseTrain f eps (-t') (-s') C (-L0/2)
  let B' := atomPulseTrain f eps s' t' C (L0/2)
  let m : ℝ := 2*(K:ℝ)*(t-s)/C
  let m' : ℝ := 2*(K:ℝ)*(t'-s')/C
  have exp (x : ℝ) : atomicWindowIncrement f eps v L0 s t x = A x+B x-m := by
    exact actualAtomicWindow_increment f he hC hT hm hs hst ht
  have exp' (x : ℝ) : atomicWindowIncrement f eps v L0 s' t' x = A' x+B' x-m' := by
    exact actualAtomicWindow_increment f he hC hT hm hs' hst' ht'
  have mean {u w : ℝ} (hu : -T≤u) (huw : u≤w) (hw : w≤T) :
      (∫ x in (0:ℝ)..1,
        atomPulseTrain f eps (-w) (-u) C (-L0/2) x+atomPulseTrain f eps u w C (L0/2) x) =
        2*(K:ℝ)*(w-u)/C := by
    rw [intervalIntegral.integral_add (atomPulseTrain_intervalIntegrable f _ _ _ _ _ he)
      (atomPulseTrain_intervalIntegrable f _ _ _ _ _ he)]
    rw [atomPulseTrain_mean f he hC hm
          (show -(T+eps/2) ≤ -w-eps/2 by linarith)
          (show -u+eps/2 ≤ T+eps/2 by linarith) (show -w≤-u by linarith),
        atomPulseTrain_mean f he hC hm
          (show -(T+eps/2) ≤ u-eps/2 by linarith)
          (show w+eps/2 ≤ T+eps/2 by linarith) huw]
    ring
  have hAC :=
    actual_same_side_correlation_budget (s:=-t) (t:=-s) (s':=-t') (t':=-s') (a:=-L0/2)
      hd g hg htβ hdim h1 h1' hv he hT hV hBv hD hm
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  dsimp only at hAC
  rw [pulseOverlap_reflect_zero] at hAC
  have hBD :=
    actual_same_side_correlation_budget (s:=s) (t:=t) (s':=s') (t':=t') (a:=L0/2)
      hd g hg htβ hdim h1 h1' hv he hT hV hBv hD hm hs hst ht hs' ht'
  dsimp only at hBD
  have hBC :=
    actual_mirror_correlation_budget (s:=s) (t:=t) (s':=-t') (t':=-s')
      (a:=L0/2) (b0:=-L0/2) hd g hg htβ hdim (by ring) hv he hT hV hBv hD hm
      hs hst ht (by linarith) (by linarith) hSafe
  dsimp only at hBC
  have hDA :=
    actual_mirror_correlation_budget (s:=s') (t:=t') (s':=-t) (t':=-s)
      (a:=L0/2) (b0:=-L0/2) hd g hg htβ hdim (by ring) hv he hT hV hBv hD hm
      hs' hst' ht' (by linarith) (by linarith) hSafe
  dsimp only at hDA
  let VolF (P Q : ℝ → ℝ) := ∫ x in (0:ℝ)..1, P x*Q x
  let O := pulseOverlap eps s t s' t' 0
  let B0 : ℝ := ((2^b:ℕ):ℝ)
  let ES := (2*(D:ℝ)+1)*(4*(2*T+eps)/B0^2)*(2*T)
  let EM := (2*(D:ℝ)+1)*(2/B0)*(2*T)
  have ac : 0 ≤ v*VolF A A'-O ∧ v*VolF A A'-O ≤ ES := hAC
  have bd : 0 ≤ v*VolF B B'-O ∧ v*VolF B B'-O ≤ ES := hBD
  have bc : 0 ≤ v*VolF B A' ∧ v*VolF B A' ≤ EM := hBC
  have da : 0 ≤ v*VolF B' A ∧ v*VolF B' A ≤ EM := hDA
  have clear : VolF A B'=VolF B' A := by unfold VolF; simp_rw [mul_comm (A _)]
  have cov := period_one_two_family_covariance (A:=A) (B:=B) (C:=A') (D:=B')
    (m:=m) (n:=m')
    (atomPulseTrain_intervalIntegrable f _ _ _ _ _ he)
    (atomPulseTrain_intervalIntegrable f _ _ _ _ _ he)
    (atomPulseTrain_intervalIntegrable f _ _ _ _ _ he)
    (atomPulseTrain_intervalIntegrable f _ _ _ _ _ he)
    (atomPulseTrain_mul_intervalIntegrable f _ _ _ _ _ _ _ _ he)
    (atomPulseTrain_mul_intervalIntegrable f _ _ _ _ _ _ _ _ he)
    (atomPulseTrain_mul_intervalIntegrable f _ _ _ _ _ _ _ _ he)
    (atomPulseTrain_mul_intervalIntegrable f _ _ _ _ _ _ _ _ he)
    (mean hs hst ht) (mean hs' hst' ht')
  change (∫ x in (0:ℝ)..1, (A x+B x-m)*(A' x+B' x-m')) =
    VolF A A'+VolF B B'+VolF B A'+VolF A B'-m*m' at cov
  have meanProd : v*(m*m')=4*(t-s)*(t'-s')/v := by
    dsimp [m,m',C]
    field_simp
    ring
  have hn : 0 ≤ 4*(t-s)*(t'-s')/v := by positivity
  have hs0 : 0 ≤ ES := by dsimp [ES]; positivity
  have hm0 : 0 ≤ EM := by dsimp [EM]; positivity
  change |v*VolF (atomicWindowIncrement f eps v L0 s t)
      (atomicWindowIncrement f eps v L0 s' t') - 2*O| ≤ 2*ES+2*EM+4*(t-s)*(t'-s')/v
  unfold VolF
  simp_rw [exp,exp']
  rw [cov,clear]
  apply abs_le.mpr
  constructor <;> nlinarith [ac.1,ac.2,bd.1,bd.2,bc.1,bc.2,da.1,da.2,meanProd]

#print axioms actual_local_atomic_covariance

end CenteredCubeSqrt
