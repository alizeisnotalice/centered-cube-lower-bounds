import IntegerCells
import ProbabilityScores
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

open MeasureTheory Set
open scoped ENNReal

namespace CenteredCube

theorem cellLaw_eq_restrict (n : ℕ) :
    RudinDensity.cellLaw n = (volume : Measure (Space n)).restrict (unitCell n) := by
  unfold RudinDensity.cellLaw RudinDensity.unitLaw unitCell
  rw [volume_pi, Measure.restrict_pi_pi]

theorem cell_shift_preserves {n : ℕ} (k : Fin n → ℤ) :
    MeasurePreserving (fun x : Space n => x-cellShift k) volume volume := by
  simpa only [sub_eq_add_neg] using
    (measurePreserving_add_right (volume : Measure (Space n)) (-cellShift k))

theorem tile_representative_inter {n : ℕ} (k : Fin n → ℤ) (E : Set (Space n)) :
    affineCell k ∩ cellRep ⁻¹' E =
      (fun x => x-cellShift k) ⁻¹' (unitCell n ∩ E) := by
  ext x
  constructor
  · rintro ⟨ht,hE⟩
    refine ⟨tile_shift_iff.mp ht,?_⟩
    change x-cellShift k ∈ E
    change cellRep x ∈ E at hE
    rwa [← cellRep_on_tile ht]
  · rintro ⟨ht,hE⟩
    have H := tile_shift_iff.mpr ht
    refine ⟨H,?_⟩
    change cellRep x ∈ E
    rwa [cellRep_on_tile H]

theorem volume_cell_event {n : ℕ} (E : Set (Space n)) (hE : MeasurableSet E)
    (k : Fin n → ℤ) :
    volume (affineCell k ∩ cellRep ⁻¹' E) = RudinDensity.cellLaw n E := by
  rw [tile_representative_inter, cellLaw_eq_restrict,
    Measure.restrict_apply hE, inter_comm E (unitCell n)]
  exact (cell_shift_preserves k).measure_preimage
    ((unitCell_measurable n).inter hE).nullMeasurableSet

theorem open_box_event_volume {n : ℕ} (L : ℤ) (N : ℕ) (E : Set (Space n))
    (hE : MeasurableSet E) :
    volume (openIntBox n L N ∩ cellRep ⁻¹' E) =
      (N:ℝ≥0∞)^n * RudinDensity.cellLaw n E := by
  classical
  letI : Fintype (boxKeys n N) := inferInstanceAs (Fintype (Fin n → Fin N))
  rw [openIntBox_partition, iUnion_inter]
  have hm : ∀ k : boxKeys n N, MeasurableSet (affineCell (translatedKey L k) ∩ cellRep ⁻¹' E) :=
    fun k => (affineCell_measurable _).inter (cellRep_measurable hE)
  have hd : Pairwise (fun k j : boxKeys n N =>
      Disjoint (affineCell (translatedKey L k) ∩ cellRep ⁻¹' E)
        (affineCell (translatedKey L j) ∩ cellRep ⁻¹' E)) := by
    intro i j hij
    exact (affineCell_pairwise L hij).mono inter_subset_left inter_subset_left
  rw [measure_iUnion hd hm]
  simp only [volume_cell_event E hE, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hh : Fintype.card (boxKeys n N) = N^n := by
    change Fintype.card (Fin n → Fin N) = N^n
    simp
  rw [hh,Nat.cast_pow]

theorem cell_integral_shift {n : ℕ} {f : Space n → ℝ≥0∞} (hfm : Measurable f)
    (hper : ∀ (k : Fin n → ℤ) x, f (x-cellShift k) = f x)
    (k : Fin n → ℤ) :
    (∫⁻ x in affineCell k, f x) = ∫⁻ x in unitCell n, f x := by
  have ht : affineCell k = (fun x : Space n => x-cellShift k) ⁻¹' unitCell n :=
    Set.ext (fun x => tile_shift_iff)
  simpa only [← ht, hper] using
    (cell_shift_preserves k).setLIntegral_comp_preimage (unitCell_measurable n) hfm

theorem open_box_integral {n : ℕ} (L : ℤ) (N : ℕ) {f : Space n → ℝ≥0∞}
    (hfm : Measurable f) (hper : ∀ (k : Fin n → ℤ) x, f (x-cellShift k) = f x) :
    (∫⁻ x in openIntBox n L N, f x) =
      (N:ℝ≥0∞)^n * (∫⁻ x in unitCell n, f x) := by
  classical
  letI : Fintype (boxKeys n N) := inferInstanceAs (Fintype (Fin n → Fin N))
  rw [openIntBox_partition, lintegral_iUnion (fun k => affineCell_measurable (translatedKey L k))
    (affineCell_pairwise L)]
  simp only [cell_integral_shift hfm hper, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hh : Fintype.card (boxKeys n N) = N^n := by
    change Fintype.card (Fin n → Fin N) = N^n
    simp
  rw [hh,Nat.cast_pow]

end CenteredCube

#print axioms CenteredCube.open_box_event_volume
#print axioms CenteredCube.open_box_integral
