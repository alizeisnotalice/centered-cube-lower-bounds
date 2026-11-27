import SqrtRawWindowCovariance
namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 900000

noncomputable def rawIntervalCount {B K : ℕ} [NeZero K] (f : ZMod K → Fin B) (h x : ℝ) :=
  (K:ℝ)*h+actualRawPrimitive f (x+h)-actualRawPrimitive f x

theorem rawIntervalCount_bounded {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    {h : ℝ} (hh : 0≤h) (hK : (K:ℝ)*h≤1) (x : ℝ) :
    0≤rawIntervalCount f h x ∧ rawIntervalCount f h x≤2 := by
  let k : ℤ := ⌊(K:ℝ)*x⌋
  let l : ℤ := ⌊(K:ℝ)*(x+h)⌋
  let r := (K:ℝ)*x-(k:ℝ)
  let s := (K:ℝ)*(x+h)-(l:ℝ)
  let u := labelCellMidpoint (f (k:ZMod K))
  let v := labelCellMidpoint (f (l:ZMod K))
  have hK0 : 0≤(K:ℝ) := by positivity
  have hkl : k≤l := Int.floor_mono (by nlinarith [mul_nonneg hK0 hh])
  have hlk : l≤k+1 := by
    have he : (K:ℝ)*(x+h)≤(K:ℝ)*x+1 := by nlinarith
    have hf := Int.floor_mono he
    have eq : (K:ℝ)*x+1=(K:ℝ)*x+((1:ℤ):ℝ) := by norm_num
    rw [eq,Int.floor_add_intCast] at hf
    exact hf
  have hd : rawIntervalCount f h x =
      ((l:ℝ)-(k:ℝ)) + (if v≤s then 1 else 0) - (if u≤r then 1 else 0) := by
    unfold rawIntervalCount
    change (K:ℝ)*h+cellPrimitive v s-cellPrimitive u r=_
    unfold cellPrimitive r s
    ring
  rw [hd]
  rcases (show l=k ∨ l=k+1 by omega) with e | e
  · have eu : v=u := by dsimp only [v,u]; rw [e]
    have hh' : r≤s := by dsimp [r,s]; rw [e]; nlinarith [mul_nonneg hK0 hh]
    have ee : (l:ℝ)=(k:ℝ) := by rw [e]
    rw [ee,sub_self,eu,zero_add]
    by_cases h' : u≤r
    · rw [ite_eq_left h',ite_eq_left (h'.trans hh')]
      norm_num
    · rw [ite_eq_right h']
      split <;> norm_num
  · have ee : (l:ℝ)-(k:ℝ)=1 := by rw [e,Int.cast_add,Int.cast_one]; ring
    rw [ee]
    split <;> split <;> norm_num

theorem rawWindow_increment_count_identity {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (L h x : ℝ) : actualRawWindow f L (x+h)-actualRawWindow f L x =
      rawIntervalCount f h (x+L/2)-rawIntervalCount f h (x-L/2) := by
  unfold actualRawWindow rawIntervalCount
  rw [show x+h+L/2=(x+L/2)+h by ring,show x+h-L/2=(x-L/2)+h by ring]
  ring

theorem rawPrimitive_shifted_period_integral {B K : ℕ} [NeZero K] (f : ZMod K → Fin B) (t : ℝ) :
    (∫ x in (0:ℝ)..1,actualRawPrimitive f (x+t)) = ∫ x in (0:ℝ)..1,actualRawPrimitive f x := by
  rw [intervalIntegral.integral_comp_add_right,zero_add,add_comm (1:ℝ),
    (actualRawPrimitive_periodic f).intervalIntegral_add_eq t 0,zero_add]

theorem rawPrimitive_shifted_integrable {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (u a b : ℝ) : IntervalIntegrable (fun x => actualRawPrimitive f (x+u)) volume a b := by
  have e := (actualRawPrimitive_intervalIntegrable f (a+u) (b+u)).comp_add_right u
  rwa [add_sub_cancel_right,add_sub_cancel_right] at e

theorem rawIntervalCount_shift {B K : ℕ} [NeZero K] (f : ZMod K → Fin B) (h t x : ℝ) :
    rawIntervalCount f h (x+t) = (K:ℝ)*h+actualRawPrimitive f (x+(t+h))-actualRawPrimitive f (x+t) := by
  unfold rawIntervalCount
  rw [add_assoc]

theorem rawIntervalCount_integrable {B K : ℕ} [NeZero K] (f : ZMod K → Fin B) (h t : ℝ) :
    IntervalIntegrable (fun x => rawIntervalCount f h (x+t)) volume 0 1 := by
  simp_rw [rawIntervalCount_shift]
  exact (intervalIntegrable_const.add (rawPrimitive_shifted_integrable f (t+h) 0 1)).sub
    (rawPrimitive_shifted_integrable f t 0 1)

theorem rawIntervalCount_period_integral {B K : ℕ} [NeZero K] (f : ZMod K → Fin B) (h t : ℝ) :
    (∫ x in (0:ℝ)..1,rawIntervalCount f h (x+t))=(K:ℝ)*h := by
  have hf (u : ℝ) : IntervalIntegrable (fun x => actualRawPrimitive f (x+u)) volume 0 1 :=
    rawPrimitive_shifted_integrable f u 0 1
  simp_rw [rawIntervalCount_shift]
  rw [intervalIntegral.integral_sub (intervalIntegrable_const.add (hf (t+h))) (hf t),
    intervalIntegral.integral_add intervalIntegrable_const (hf (t+h)),
    rawPrimitive_shifted_period_integral,rawPrimitive_shifted_period_integral,intervalIntegral.integral_const]
  simp

#print axioms rawIntervalCount_bounded
#print axioms rawIntervalCount_period_integral
end CenteredCubeSqrt
