import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import MutualEvaluation.Internal.CertificationCollisionBound
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.CongrExclamation

/-! Internal finite-product and random-table coupling lemmas. -/
noncomputable section
namespace MutualEvaluation.Certification.Collision
open Finset Classical

variable {A I J : Type*} [Fintype A] [Fintype I] [Fintype J]

def weight (w : A → ℝ) (s : I → A) : ℝ := ∏ i, w (s i)

def probability (w : A → ℝ) (E : (I → A) → Prop) : ℝ :=
  ∑ s, weight w s * if E s then 1 else 0

omit [Fintype A] in
lemma weight_nonneg (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (s : I → A) :
    0 ≤ weight w s := Finset.prod_nonneg fun i _ => hw (s i)

lemma weight_sum (w : A → ℝ) (hw : ∑ a, w a = 1) :
    ∑ s : I → A, weight w s = 1 := by
  classical
  simpa only [weight, hw, Finset.prod_const_one] using
    (Fintype.prod_sum (fun (_ : I) a => w a)).symm

lemma fiber_product (u : I → J) (g : I → ℝ) :
    (∏ j, ∏ i ∈ Finset.univ.filter (fun i => u i = j), g i) = ∏ i, g i := by
  classical
  exact Finset.prod_fiberwise Finset.univ u g

lemma weight_fiber (w : A → ℝ) (hw : ∑ a, w a = 1)
    (u : I → J) (hu : Function.Injective u) (s : I → A) :
    (∑ z : J → A, weight w z * if (fun i => z (u i)) = s then 1 else 0) =
      weight w s := by
  classical
  let r : J → A → ℝ := fun j a => w a *
    ∏ i ∈ Finset.univ.filter (fun i => u i = j), if a = s i then 1 else 0
  have hrs (j : J) : (∑ a, r j a) =
      ∏ i ∈ Finset.univ.filter (fun i => u i = j), w (s i) := by
    by_cases hj : ∃ i, u i = j
    · obtain ⟨i, rfl⟩ := hj
      have hf : Finset.univ.filter (fun k => u k = u i) = {i} := by
        ext k
        simp [hu.eq_iff]
      simp [r, hf]
    · have hf : Finset.univ.filter (fun i => u i = j) = ∅ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        exact fun hi => hj ⟨i, hi⟩
      simp [r, hf, hw]
  have hrp (z : J → A) : (∏ j, r j (z j)) =
      weight w z * if (fun i => z (u i)) = s then 1 else 0 := by
    simp only [r, Finset.prod_mul_distrib]
    have hp : (∏ j, ∏ i ∈ Finset.univ.filter (fun i => u i = j),
        if z j = s i then (1 : ℝ) else 0) =
        ∏ i, if z (u i) = s i then (1 : ℝ) else 0 := by
      calc
        _ = ∏ j, ∏ i ∈ Finset.univ.filter (fun i => u i = j),
            if z (u i) = s i then (1 : ℝ) else 0 := by
          apply Finset.prod_congr rfl
          intro j _
          apply Finset.prod_congr rfl
          intro i hi
          rw [(Finset.mem_filter.mp hi).2]
        _ = _ := fiber_product u _
    rw [hp, Fintype.prod_boole]
    simp only [weight, funext_iff]
  calc
    _ = ∑ z : J → A, ∏ j, r j (z j) := Finset.sum_congr rfl fun z _ => (hrp z).symm
    _ = ∏ j, ∑ a, r j a := (Fintype.prod_sum r).symm
    _ = ∏ i, w (s i) := by simp_rw [hrs]; exact fiber_product u _
    _ = _ := rfl

lemma probability_nonneg (w : A → ℝ) (hw : ∀ a, 0 ≤ w a)
    (E : (I → A) → Prop) : 0 ≤ probability w E := by
  classical
  apply Finset.sum_nonneg
  intro s _
  exact mul_nonneg (weight_nonneg w hw s) (by split_ifs <;> norm_num)

lemma probability_mono (w : A → ℝ) (hw : ∀ a, 0 ≤ w a)
    (E F : (I → A) → Prop) (hEF : ∀ s, E s → F s) :
    probability w E ≤ probability w F := by
  classical
  apply Finset.sum_le_sum
  intro s _
  apply mul_le_mul_of_nonneg_left _ (weight_nonneg w hw s)
  split_ifs with he hf hf <;> simp_all

lemma probability_le_one (w : A → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : ∑ a, w a = 1) (E : (I → A) → Prop) : probability w E ≤ 1 := by
  classical
  calc
    probability w E ≤ ∑ s : I → A, weight w s := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_of_le_one_right (weight_nonneg w hw s) (by split_ifs <;> norm_num)
    _ = 1 := weight_sum w hs

lemma injective_probability (w : A → ℝ) (hw : ∑ a, w a = 1)
    (u : I → J) (hu : Function.Injective u) (E : (I → A) → Prop) :
    (∑ z : J → A, weight w z * if E (fun i => z (u i)) then 1 else 0) =
      probability w E := by
  classical
  have h (z : J → A) :
      (if E (fun i => z (u i)) then (1 : ℝ) else 0) =
        ∑ s : I → A, (if (fun i => z (u i)) = s then (1 : ℝ) else 0) *
          (if E s then 1 else 0) := by
    simp only [ite_mul, one_mul, zero_mul]
    simp
  simp_rw [h, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, weight_fiber w hw u hu]
  rfl

def empirical (c : ℝ) (z : J → A) (a : A) : ℝ :=
  ∑ j, c * if z j = a then 1 else 0

lemma empirical_probability (c : ℝ) (z : J → A) (E : (I → A) → Prop) :
    probability (empirical c z) E =
      ∑ u : I → J, weight (fun _ => c) u * if E (fun i => z (u i)) then 1 else 0 := by
  classical
  have hw (s : I → A) : weight (empirical c z) s =
      ∑ u : I → J, weight (fun _ => c) u *
        if (fun i => z (u i)) = s then 1 else 0 := by
    unfold weight empirical
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.prod_mul_distrib, Fintype.prod_boole]
    simp only [funext_iff]
  unfold probability
  simp_rw [hw, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp_rw [mul_assoc, ← Finset.mul_sum]
  simp only [ite_mul, one_mul, zero_mul]
  simp

lemma random_table_coupling (w : A → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : ∑ a, w a = 1) (c : ℝ) (hc : 0 ≤ c) (hcs : ∑ _ : J, c = 1)
    (E : (I → A) → Prop) :
    probability w E ≤
      (∑ z : J → A, weight w z * probability (empirical c z) E) +
      ∑ u : I → J, if ¬Function.Injective u then weight (fun _ : J => c) u else 0 := by
  classical
  let a : (I → J) → ℝ := fun u =>
    ∑ z : J → A, weight w z * if E (fun i => z (u i)) then 1 else 0
  have ha (u : I → J) : 0 ≤ a u :=
    Finset.sum_nonneg fun z _ => mul_nonneg (weight_nonneg w hw z)
      (by split_ifs <;> norm_num)
  have hpoint (u : I → J) : probability w E ≤ a u +
      if ¬Function.Injective u then (1 : ℝ) else 0 := by
    by_cases hu : Function.Injective u
    · simp only [hu, not_true_eq_false, ↓reduceIte, add_zero]
      exact le_of_eq (injective_probability w hs u hu E).symm
    · simp only [hu, not_false_eq_true, ↓reduceIte]
      exact (probability_le_one w hw hs E).trans (by linarith [ha u])
  have hsum := Finset.sum_le_sum (fun (u : I → J) (_ : u ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hpoint u) (weight_nonneg (fun _ : J => c) (fun _ => hc) u))
  have hl : (∑ u : I → J, weight (fun _ : J => c) u * probability w E) =
      probability w E := by
    rw [← Finset.sum_mul, weight_sum _ hcs, one_mul]
  have hr : (∑ u : I → J, weight (fun _ : J => c) u * a u) =
      ∑ z : J → A, weight w z * probability (empirical c z) E := by
    simp_rw [a, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    rw [empirical_probability, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring
  simp only [hl, mul_add, Finset.sum_add_distrib] at hsum
  rw [hr] at hsum
  simpa only [mul_ite, mul_one, mul_zero] using hsum

lemma confidence_transfer (w : A → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : ∑ a, w a = 1) (c : ℝ) (hc : 0 ≤ c) (hcs : ∑ _ : J, c = 1)
    (E : (I → A) → Prop) (δ : ℝ)
    (hvalid : ∀ z : J → A, probability (empirical c z) E ≤ δ) :
    probability w E ≤ δ +
      ∑ u : I → J, if ¬Function.Injective u then weight (fun _ : J => c) u else 0 := by
  apply (random_table_coupling w hw hs c hc hcs E).trans
  refine add_le_add ?_ le_rfl
  calc
    (∑ z : J → A, weight w z * probability (empirical c z) E) ≤
        ∑ z : J → A, weight w z * δ :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hvalid z) (weight_nonneg w hw z)
    _ = δ := by rw [← Finset.sum_mul, weight_sum w hs, one_mul]

lemma uniform_sum (m : ℕ) (hm : 0 < m) : ∑ _ : Fin m, (m : ℝ)⁻¹ = 1 := by
  simpa using mul_inv_cancel₀ (show (m : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hm)

lemma finite_random_table_coupling (w : A → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : ∑ a, w a = 1) (m n : ℕ) (hm : 0 < m)
    (E : (Fin n → A) → Prop) :
    probability w E ≤
      (∑ z : Fin m → A, weight w z * probability (empirical (m : ℝ)⁻¹ z) E) +
      (Nat.choose n 2 : ℝ) / (m : ℝ) := by
  classical
  apply (random_table_coupling w hw hs (m : ℝ)⁻¹
    (inv_nonneg.mpr (Nat.cast_nonneg m)) (uniform_sum m hm) E).trans
  refine add_le_add ?_ ?_
  · apply le_of_eq
    congr!
  · convert! Internal.collision_sum_le m n hm using 1
    simp [weight]
    congr!

lemma finite_confidence_transfer (w : A → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : ∑ a, w a = 1) (m n : ℕ) (hm : 0 < m)
    (E : (Fin n → A) → Prop) (δ : ℝ)
    (hvalid : ∀ z : Fin m → A, probability (empirical (m : ℝ)⁻¹ z) E ≤ δ) :
    probability w E ≤ δ + (Nat.choose n 2 : ℝ) / (m : ℝ) := by
  classical
  apply (confidence_transfer w hw hs (m : ℝ)⁻¹
    (inv_nonneg.mpr (Nat.cast_nonneg m)) (uniform_sum m hm) E δ hvalid).trans
  refine add_le_add ?_ ?_
  · apply le_of_eq
    congr!
  · convert! Internal.collision_sum_le m n hm using 1
    simp [weight]
    congr!

lemma collision_constant_exact {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    (Nat.choose n 2 : ℝ) / ((2 * k * n ^ 2 : ℕ) : ℝ) =
      ((n : ℝ) - 1) / (4 * (k : ℝ) * (n : ℝ)) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [Nat.cast_choose_two]
  push_cast
  field_simp
  ring

lemma collision_constant_stronger {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    (Nat.choose n 2 : ℝ) / ((2 * k * n ^ 2 : ℕ) : ℝ) ≤
      1 / (4 * (k : ℝ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [collision_constant_exact hk hn]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

end MutualEvaluation.Certification.Collision
