import SqrtKernelDiagonal
import Mathlib.Analysis.Real.Sqrt

namespace CenteredCubeSqrt

theorem sqrtProduct_lipschitz_one_sided {a b a' b' e : ℝ}
    (he : 0≤e) (ha : 1/4≤a) (hb : 1/4≤b)
    (ha' : 0≤a') (hb' : 0≤b') (hA : a' ≤ a+e) (hB : b' ≤ b+e) :
    Real.sqrt (a'*b') ≤ (1+4*e)*Real.sqrt (a*b) := by
  have A : a'≤(1+4*e)*a := by
    have h := mul_le_mul_of_nonneg_left ha (show 0≤4*e by positivity)
    nlinarith
  have B : b'≤(1+4*e)*b := by
    have h := mul_le_mul_of_nonneg_left hb (show 0≤4*e by positivity)
    nlinarith
  have he' : 0≤1+4*e := by positivity
  calc
    _ ≤ Real.sqrt (((1+4*e)*a)*((1+4*e)*b)) :=
      Real.sqrt_le_sqrt (mul_le_mul A B hb' (by nlinarith))
    _ = _ := by
      rw [show (1+4*e)*a*((1+4*e)*b)=(1+4*e)^2*(a*b) by ring,
        Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq he']

theorem normalizedEntry_le_eight {a b a' b' c c' e : ℝ}
    (ha : 1/4≤a) (hb : 1/4≤b) (ha' : 1/4≤a') (hb' : 1/4≤b')
    (hA : |a-a'|≤e) (hB : |b-b'|≤e) (hC : |c-c'|≤e)
    (hc : |c|≤Real.sqrt (a*b)) (hc' : |c'|≤Real.sqrt (a'*b')) :
    |c/Real.sqrt (a*b)-c'/Real.sqrt (a'*b')|≤8*e := by
  have he : 0≤e := (abs_nonneg _).trans hA
  have he4 : 0≤4*e := by positivity
  have aux {x y z w : ℝ} (_hx : 1/4≤x) (hy : 1/4≤y)
      (hxy : y≤x) (hlarge : x≤(1+4*e)*y)
      (hzz : |z|≤x) (hzw : |z-w|≤e) :
      |z/x-w/y|≤8*e := by
    have hy0 : 0<y := by linarith
    have hx0 : 0<x := by linarith
    have ee : z/x-w/y=(z-w)/y+(z/x)*(1-x/y) := by field_simp [hy0.ne',hx0.ne']; ring
    rw [ee]
    refine (abs_add_le _ _).trans ?_
    have h1 : |(z-w)/y|≤4*e := by
      rw [abs_div,abs_of_pos hy0]
      apply (div_le_iff₀ hy0).mpr
      exact hzw.trans (by nlinarith [mul_le_mul_of_nonneg_left hy he4])
    have h2 : |z/x*(1-x/y)|≤4*e := by
      rw [abs_mul,abs_div,abs_of_pos hx0,
        abs_of_nonpos (sub_nonpos.mpr ((le_div_iff₀ hy0).mpr (by simpa using hxy)))]
      have h1' : |z|/x≤1 := (div_le_one hx0).mpr hzz
      have hh : 0≤ -(1-x/y) := by
        exact neg_nonneg.mpr (sub_nonpos.mpr ((le_div_iff₀ hy0).mpr (by simpa using hxy)))
      have h2' : -(1-x/y)≤4*e := by
        have hxx := (div_le_iff₀ hy0).mpr hlarge
        linarith
      calc
        _ ≤ -(1-x/y) := mul_le_of_le_one_left hh h1'
        _ ≤ _ := h2'
    linarith
  have hh {u v : ℝ} (hu : 1/4≤u) (hv : 1/4≤v) : 1/4≤Real.sqrt (u*v) := by
    have hp : (1/4:ℝ)^2≤u*v := by
      rw [pow_two]
      exact mul_le_mul hu hv (by norm_num) (by linarith)
    have e : Real.sqrt ((1/4:ℝ)^2)=1/4 := Real.sqrt_sq (by norm_num)
    exact e ▸ Real.sqrt_le_sqrt hp
  have hx := hh ha hb
  have hy := hh ha' hb'
  have h1 := sqrtProduct_lipschitz_one_sided he ha hb (by linarith : 0≤a') (by linarith : 0≤b')
    (by linarith [(abs_le.mp hA).1] : a'≤a+e) (by linarith [(abs_le.mp hB).1] : b'≤b+e)
  have h2 := sqrtProduct_lipschitz_one_sided he ha' hb' (by linarith : 0≤a) (by linarith : 0≤b)
    (by linarith [(abs_le.mp hA).2] : a≤a'+e) (by linarith [(abs_le.mp hB).2] : b≤b'+e)
  rcases le_total (Real.sqrt (a*b)) (Real.sqrt (a'*b')) with h | h
  · rw [abs_sub_comm]
    rw [abs_sub_comm c c'] at hC
    exact aux hy hx h h1 hc' hC
  · exact aux hx hy h h2 hc hC

#print axioms normalizedEntry_le_eight

end CenteredCubeSqrt
