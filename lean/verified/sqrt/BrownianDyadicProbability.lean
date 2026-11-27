import BrownianIncrementControl

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace CubeBrownian

private theorem tail_limit_series (C q : ℝ) (hq0 : 0 ≤ q) (hq : q < 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (E : ℕ → Set Ω)
    (h : ∀ m, μ (E m) ≤ ENNReal.ofReal (C*q^m)) :
    ∀ᵐ ω ∂μ, ∀ᶠ m in atTop, ω ∉ E m := by
  apply ae_eventually_notMem
  have H := (summable_geometric_of_lt_one hq0 hq).mul_left C
  exact ne_top_of_le_ne_top H.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum h)

theorem preBrownian_ae_dyadic_grid {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {μ : Measure Ω} (hB : IsPreBrownianReal B μ)
    (clock : ℕ → ℕ → ℝ≥0)
    (hc : ∀ m k, |(clock m (k+1):ℝ) - (clock m k:ℝ)| ≤ (1/2:ℝ)^m) :
    ∀ᵐ ω ∂μ, ∀ M : ℕ, ∀ᶠ m in atTop, ∀ k < M*2^m,
      |B (clock m (k+1)) ω - B (clock m k) ω| ≤ (7/8:ℝ)^m := by
  rw [ae_all_iff]
  intro M
  let E (m : ℕ) : Set Ω := ⋃ k : Fin (M*2^m), {ω |
    (7/8:ℝ)^m < |B (clock m (k.1+1)) ω - B (clock m k.1) ω|}
  let q : ℝ := (1/2)/((7/8)^4)
  have hq0 : 0 ≤ q := by norm_num [q]
  have hq : q < 1 := by norm_num [q]
  have hE (m : ℕ) : μ (E m) ≤ ENNReal.ofReal ((M:ℝ)*stdBrownianFourth*q^m) := by
    change μ (⋃ k : Fin (M*2^m), _) ≤ _
    refine (measure_iUnion_fintype_le μ _).trans ?_
    have e (k : Fin (M*2^m)) : μ {ω | (7/8:ℝ)^m <
          |B (clock m (k.1+1)) ω-B (clock m k.1) ω|} ≤
        ENNReal.ofReal (stdBrownianFourth*((1/2:ℝ)^m)^2/((7/8:ℝ)^m)^4) := by
      refine (preBrownian_increment_tail hB (clock m (k.1+1)) (clock m k.1)
        (by positivity : 0 < (7/8:ℝ)^m)).trans (ENNReal.ofReal_le_ofReal ?_)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) (hc m k.1) 2) stdBrownianFourth_nonneg) (by positivity)
    refine (Finset.sum_le_sum (fun k _ => e k)).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    dsimp [q]
    have H : ((2:ℝ)^m)*(((1/2:ℝ)^m)^2)/(((7/8:ℝ)^m)^4) =
        ((1/2:ℝ)/((7/8:ℝ)^4))^m := by
      have hp (a : ℝ) (k : ℕ) : (a^m)^k = (a^k)^m := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      rw [hp (1/2) 2, hp (7/8) 4, ← mul_pow, ← div_pow]
      norm_num
    calc
      _ = (M:ℝ)*stdBrownianFourth * (((2:ℝ)^m)*(((1/2:ℝ)^m)^2)/(((7/8:ℝ)^m)^4)) := by ring
      _ ≤ _ := by rw [H]
  filter_upwards [tail_limit_series ((M:ℝ)*stdBrownianFourth) q hq0 hq μ E hE] with ω hw
  filter_upwards [hw] with m hm k hk
  apply le_of_not_gt
  intro hf
  exact hm (Set.mem_iUnion.2 ⟨⟨k,hk⟩,hf⟩)

theorem preBrownian_ae_dyadic_approx {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {μ : Measure Ω} (hB : IsPreBrownianReal B μ)
    (t : ℝ≥0) (tseq : ℕ → ℝ≥0)
    (hd : ∀ m, |(tseq m:ℝ)-(t:ℝ)| ≤ (1/2:ℝ)^m) :
    ∀ᵐ ω ∂μ, Tendsto (fun m => B (tseq m) ω) atTop (𝓝 (B t ω)) := by
  let E (m : ℕ) : Set Ω := {ω| (7/8:ℝ)^m < |B (tseq m) ω-B t ω|}
  let q : ℝ := ((1/2)^2)/((7/8)^4)
  have hE (m : ℕ) : μ (E m) ≤ ENNReal.ofReal (stdBrownianFourth*q^m) := by
    refine (preBrownian_increment_tail hB (tseq m) t
      (by positivity : 0 < (7/8:ℝ)^m)).trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      _ ≤ stdBrownianFourth*((1/2:ℝ)^m)^2/((7/8:ℝ)^m)^4 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg _) (hd m) 2) stdBrownianFourth_nonneg) (by positivity)
      _ = _ := by
        have H : (((1/2:ℝ)^m)^2)/(((7/8:ℝ)^m)^4) = q^m := by
          dsimp [q]
          have hp (a : ℝ) (k : ℕ) : (a^m)^k = (a^k)^m := by
            rw [← pow_mul, ← pow_mul, Nat.mul_comm]
          rw [hp (1/2) 2, hp (7/8) 4, ← div_pow]
        calc
          _ = stdBrownianFourth* ((((1/2:ℝ)^m)^2)/(((7/8:ℝ)^m)^4)) := by ring
          _ = _ := by rw [H]
  filter_upwards [tail_limit_series stdBrownianFourth q (by norm_num [q]) (by norm_num [q]) μ E hE] with ω hω
  refine tendsto_iff_dist_tendsto_zero.2 ?_
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤7/8) (by norm_num))
  · exact Eventually.of_forall (fun _ => dist_nonneg)
  · filter_upwards [hω] with m hm
    rw [Real.dist_eq]
    exact le_of_not_gt (show ¬ (7/8:ℝ)^m < |B (tseq m) ω-B t ω| from hm)

#print axioms preBrownian_ae_dyadic_grid
#print axioms preBrownian_ae_dyadic_approx
end CubeBrownian
