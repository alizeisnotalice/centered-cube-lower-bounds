import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Real.Lemmas

open Set Filter
open scoped Topology
namespace CubeBrownian

/-- Uniform convergence over moving sets of safe base points. The only compact
quantity is the actual parameter λ; no compactness of the safe base is required. -/
theorem uniform_of_compact_parameter_sequential
    {α β : Type*} [TopologicalSpace β] [FirstCountableTopology β]
    (K : Set β) (hK : IsCompact K) (safe : ℕ → α → Prop)
    (param : ℕ → α → β) (err : ℕ → α → ℝ)
    (hparam : ∀ n x, safe n x → param n x ∈ K)
    (hSeq : ∀ (m : ℕ → ℕ) (x : ℕ → α), Tendsto m atTop atTop →
      (∀ n, safe (m n) (x n)) →
      ∀ y ∈ K, Tendsto (fun n ↦ param (m n) (x n)) atTop (𝓝 y) →
      Tendsto (fun n ↦ err (m n) (x n)) atTop (𝓝 0))
    (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x, safe n x → |err n x| < ε := by
  classical
  by_contra hNo
  have hf : ∃ᶠ n in atTop, ∃ x, safe n x ∧ ε ≤ |err n x| := by
    intro H
    apply hNo
    filter_upwards [H] with n hn x hx
    exact lt_of_not_ge (fun h ↦ hn ⟨x,hx,h⟩)
  have H := frequently_atTop.mp hf
  choose m hm x hx hε using H
  obtain ⟨a,ha,φ,hφ,hConv⟩ := hK.tendsto_subseq (fun n ↦ hparam (m n) (x n) (hx n))
  have hmT : Tendsto m atTop atTop := tendsto_atTop_mono hm tendsto_id
  have hL := hSeq (m ∘ φ) (x ∘ φ) (hmT.comp hφ.tendsto_atTop) (fun n ↦ hx (φ n))
    a ha hConv
  have hlt : ∀ᶠ n in atTop, |err ((m ∘ φ) n) ((x ∘ φ) n)| < ε := by
    have hAbs : Tendsto (fun n ↦ |err ((m ∘ φ) n) ((x ∘ φ) n)|) atTop (𝓝 0) := by
      simpa only [abs_zero] using hL.abs
    exact hAbs.eventually_lt_const he
  obtain ⟨n,hn⟩ := hlt.exists
  exact (not_le_of_gt hn) (hε (φ n))

end CubeBrownian
#print axioms CubeBrownian.uniform_of_compact_parameter_sequential
