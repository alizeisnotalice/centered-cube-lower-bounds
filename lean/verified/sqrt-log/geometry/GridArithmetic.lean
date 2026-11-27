import GridUnion
import Mathlib.Algebra.Order.Floor.Semiring

namespace CenteredCube.RudinDensity

noncomputable def paperGridQ (K : ℕ) (a : ℝ) : ℕ := ⌊(K:ℝ)/(100*a)⌋₊

noncomputable def paperGridM (K : ℕ) (a : ℝ) : ℕ := 2*paperGridQ K a + 1

noncomputable def paperGrid (K : ℕ) (a u : ℝ) (i : ℕ) : ℝ :=
  (K:ℝ)/4 + ((i:ℝ)-(paperGridQ K a:ℝ))*(a/u)

theorem paperGrid_card_bound (K : ℕ) {a : ℝ} (ha : 0 < a)
    (h : 2 ≤ (K:ℝ)/(100*a)) :
    (K:ℝ)/(100*a) ≤ (paperGridM K a:ℝ) ∧
      (paperGridM K a:ℝ) ≤ 3*((K:ℝ)/(100*a)) := by
  unfold paperGridM paperGridQ
  push_cast
  have h₁ := Nat.floor_le (show 0 ≤ (K:ℝ)/(100*a) by positivity)
  have h₂ := Nat.lt_floor_add_one ((K:ℝ)/(100*a))
  constructor <;> linarith

theorem paperGrid_window (K : ℕ) {a u : ℝ} (ha : 0 < a) (hu : 0 < u)
    {i : ℕ} (hi : i < paperGridM K a) :
    |paperGrid K a u i-(K:ℝ)/4| ≤ (K:ℝ)/(100*u) := by
  have hi1 : (i:ℝ) ≤ 2*(paperGridQ K a:ℝ) := by
    unfold paperGridM at hi
    exact_mod_cast (show i ≤ 2*paperGridQ K a by omega)
  have hi0 : 0 ≤ (i:ℝ) := by positivity
  have hQ : (paperGridQ K a:ℝ) ≤ (K:ℝ)/(100*a) :=
    Nat.floor_le (by positivity)
  have hab : |(i:ℝ)-(paperGridQ K a:ℝ)| ≤ (paperGridQ K a:ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  unfold paperGrid
  rw [add_sub_cancel_left, abs_mul, abs_of_pos (div_pos ha hu)]
  have he : (K:ℝ)/(100*a)*(a/u) = (K:ℝ)/(100*u) := by field_simp
  rw [← he]
  exact mul_le_mul_of_nonneg_right (hab.trans hQ) (by positivity)

theorem paperGrid_lag (K : ℕ) {a u : ℝ} (ha : 0 < a) (hu : 0 < u)
    {i j : ℕ} (hij : i < j) :
    |paperGrid K a u i-paperGrid K a u j| = ((j-i:ℕ):ℝ)*a/u := by
  have h : (i:ℝ) ≤ (j:ℝ) := by exact_mod_cast hij.le
  have hcast : ((j-i:ℕ):ℝ) = (j:ℝ)-(i:ℝ) := Nat.cast_sub hij.le
  unfold paperGrid
  rw [show ((K:ℝ)/4 + ((i:ℝ)-(paperGridQ K a:ℝ))*(a/u)) -
        ((K:ℝ)/4 + ((j:ℝ)-(paperGridQ K a:ℝ))*(a/u)) =
        ((i:ℝ)-(j:ℝ))*(a/u) by ring,
      abs_mul, abs_of_nonpos (sub_nonpos.mpr h), abs_of_pos (div_pos ha hu), hcast]
  ring

noncomputable def roundedFour (A : ℝ) : ℕ := 4 * ⌊A/4+1/2⌋₊

theorem roundedFour_divisible (A : ℝ) : 4 ∣ roundedFour A :=
  ⟨⌊A/4+1/2⌋₊, rfl⟩

theorem roundedFour_error {A : ℝ} (hA : 0 ≤ A) : |(roundedFour A:ℝ)-A| ≤ 2 := by
  unfold roundedFour
  push_cast
  have hi := Nat.floor_le (show 0 ≤ A/4+1/2 by linarith)
  have hj := Nat.lt_floor_add_one (A/4+1/2)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

noncomputable def paperA (n : ℕ) : ℝ :=
  Real.sqrt (n:ℝ) / (90*Real.pi*Real.sqrt (Real.log (n:ℝ)))

noncomputable def paperK (n : ℕ) : ℕ := roundedFour (paperA n)

noncomputable def paperU (n : ℕ) : ℝ :=
  Real.sqrt (n:ℝ) / (90*Real.pi*(paperK n:ℝ))

theorem paperK_center_relation {n : ℕ} (hn : 0 < n) (hK : 0 < paperK n) :
    (paperK n:ℝ) = Real.sqrt (n:ℝ)/(90*Real.pi*paperU n) := by
  unfold paperU
  have h₁ : (paperK n:ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have h₂ : Real.sqrt (n:ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
  field_simp [Real.pi_pos.ne']
  <;> ring

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.paperGrid_card_bound
#print axioms CenteredCube.RudinDensity.paperGrid_window
#print axioms CenteredCube.RudinDensity.paperGrid_lag
#print axioms CenteredCube.RudinDensity.roundedFour_error
#print axioms CenteredCube.RudinDensity.paperK_center_relation
