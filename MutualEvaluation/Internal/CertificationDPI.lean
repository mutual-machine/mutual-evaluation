import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Internal finite Jensen data processing and the uniform latent bound. -/
noncomputable section
open scoped BigOperators
namespace MutualEvaluation.Certification.Proofs

variable {A B : Type} [Fintype A] [Fintype B]

def divergence (f : ℝ → ℝ) (p q : A → ℝ) : ℝ :=
  ∑ a, q a * f (p a / q a)

lemma perspective_sum_le (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ici 0) f)
    (p q : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hac : ∀ a, q a = 0 → p a = 0) :
    (∑ a, q a) * f ((∑ a, p a) / (∑ a, q a)) ≤ ∑ a, q a * f (p a / q a) := by
  classical
  let s := ∑ a, q a
  have hs : 0 ≤ s := Finset.sum_nonneg fun a _ => hq a
  by_cases hz : s = 0
  · have hqz : ∀ a, q a = 0 := by
      intro a
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hq a)).mp hz a (Finset.mem_univ a)
    have hpz : ∀ a, p a = 0 := fun a => hac a (hqz a)
    simp [hqz, hpz]
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
    have hw : ∑ a, q a / s = 1 := by rw [← Finset.sum_div]; exact div_self hz
    have he : (∑ a, (q a / s) * (p a / q a)) = (∑ a, p a) / s := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hqa : q a = 0
      · simp [hqa, hac a hqa]
      · field_simp
    have hj := hf.map_sum_le (t := Finset.univ) (w := fun a => q a / s)
      (p := fun a => p a / q a) (fun a _ => div_nonneg (hq a) hs)
      hw (fun a _ => div_nonneg (hp a) (hq a))
    simp only [smul_eq_mul] at hj
    rw [he] at hj
    have hmul := mul_le_mul_of_nonneg_left hj hs
    convert hmul using 1
    · rfl
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      field_simp

 theorem divergence_dataProcessing (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ici 0) f)
    (p q : A → ℝ) (k : A → B → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hac : ∀ a, q a = 0 → p a = 0)
    (hk : ∀ a b, 0 ≤ k a b) (hks : ∀ a, ∑ b, k a b = 1) :
    divergence f (fun b => ∑ a, p a * k a b) (fun b => ∑ a, q a * k a b) ≤
      divergence f p q := by
  classical
  unfold divergence
  calc
    _ ≤ ∑ b, ∑ a, (q a * k a b) * f ((p a * k a b) / (q a * k a b)) := by
      apply Finset.sum_le_sum
      intro b _
      apply perspective_sum_le f hf
      · intro a; exact mul_nonneg (hp a) (hk a b)
      · intro a; exact mul_nonneg (hq a) (hk a b)
      · intro a ha
        rcases mul_eq_zero.mp ha with h | h
        · simp [hac a h]
        · simp [h]
    _ = ∑ a, q a * f (p a / q a) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      calc
        _ = ∑ b, k a b * (q a * f (p a / q a)) := by
          apply Finset.sum_congr rfl
          intro b _
          by_cases hb : k a b = 0
          · simp [hb]
          · rw [mul_div_mul_right _ _ hb]; ring
        _ = _ := by rw [← Finset.sum_mul, hks]; simp


lemma uniform_diagonal_divergence {m : ℕ} [NeZero m] (f : ℝ → ℝ) :
    divergence f (fun ij : Fin m × Fin m => if ij.1 = ij.2 then (m : ℝ)⁻¹ else 0)
      (fun _ => (m : ℝ)⁻¹ * (m : ℝ)⁻¹) =
      f m / m + (1 - 1 / (m : ℝ)) * f 0 := by
  classical
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  let d : ℝ := (m : ℝ)⁻¹
  let p : Fin m × Fin m → ℝ := fun ij => if ij.1 = ij.2 then d else 0
  let q : Fin m × Fin m → ℝ := fun _ => d * d
  change divergence f p q = _
  unfold divergence
  have term : ∀ ij : Fin m × Fin m,
      q ij * f (p ij / q ij) = d * d * f 0 + if ij.1 = ij.2 then d * d * (f m - f 0) else 0 := by
    intro ij
    dsimp [p, q]
    by_cases h : ij.1 = ij.2
    · simp only [h, if_true]
      have hr : d / (d * d) = (m : ℝ) := by dsimp [d]; field_simp
      rw [hr]; ring
    · simp [h]
  simp_rw [term]
  rw [Finset.sum_add_distrib]
  simp only [Fintype.sum_prod_type, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_prod, nsmul_eq_mul]
  dsimp [d]
  field_simp
  push_cast
  ring


lemma uniform_latent_weights_bound {m : ℕ} [NeZero m]
    (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ici 0) f)
    (kx : Fin m → A → ℝ) (ky : Fin m → B → ℝ)
    (hx : ∀ i a, 0 ≤ kx i a) (hy : ∀ i b, 0 ≤ ky i b)
    (hxs : ∀ i, ∑ a, kx i a = 1) (hys : ∀ i, ∑ b, ky i b = 1) :
    divergence f (fun ab : A × B => (∑ i, kx i ab.1 * ky i ab.2) / m)
      (fun ab => ((∑ i, kx i ab.1) / m) * ((∑ i, ky i ab.2) / m)) ≤
      f m / m + (1 - 1 / (m : ℝ)) * f 0 := by
  classical
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  let d : ℝ := (m : ℝ)⁻¹
  have hd : 0 ≤ d := inv_nonneg.mpr (Nat.cast_nonneg m)
  have hdn : d ≠ 0 := inv_ne_zero hm
  let p : Fin m × Fin m → ℝ := fun ij => if ij.1 = ij.2 then d else 0
  let q : Fin m × Fin m → ℝ := fun _ => d * d
  let k : (Fin m × Fin m) → (A × B) → ℝ := fun ij ab => kx ij.1 ab.1 * ky ij.2 ab.2
  have hk : ∀ ij ab, 0 ≤ k ij ab := fun ij ab => mul_nonneg (hx _ _) (hy _ _)
  have hks : ∀ ij, ∑ ab, k ij ab = 1 := by
    intro ij
    simp only [k, Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hys, mul_one]
    exact hxs _
  have H := divergence_dataProcessing f hf p q k
    (fun ij => by dsimp [p]; split_ifs <;> positivity)
    (fun _ => mul_nonneg hd hd)
    (fun ij h => False.elim ((mul_ne_zero hdn hdn) h)) hk hks
  have hP : (fun ab => ∑ ij, p ij * k ij ab) =
      (fun ab : A × B => (∑ i, kx i ab.1 * ky i ab.2) / m) := by
    funext ab
    simp only [p, k, Fintype.sum_prod_type, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.mul_sum]
    dsimp [d]
    ring
  have hQ : (fun ab => ∑ ij, q ij * k ij ab) =
      (fun ab : A × B => ((∑ i, kx i ab.1) / m) * ((∑ i, ky i ab.2) / m)) := by
    funext ab
    simp only [q, k, Fintype.sum_prod_type]
    simp_rw [← mul_assoc, ← Finset.mul_sum]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    dsimp [d]
    ring
  rw [hP, hQ] at H
  convert H using 1
  exact (uniform_diagonal_divergence f).symm

lemma quartic_convex : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ => (t - 1) ^ 4) := by
  have h : ConvexOn ℝ Set.univ (fun t : ℝ => t ^ 4) :=
    (show Even (4 : ℕ) by decide).convexOn_pow
  have ht : ConvexOn ℝ Set.univ (fun t : ℝ => (t - 1) ^ 4) := by
    simpa only [Set.preimage_univ, sub_eq_add_neg, Function.comp_def, add_comm] using h.translate_right (-1)
  exact ht.subset (Set.subset_univ _) (convex_Ici _)

lemma quartic_normalized : (fun t : ℝ => (t - 1) ^ 4) 1 = 0 := by norm_num

end MutualEvaluation.Certification.Proofs
