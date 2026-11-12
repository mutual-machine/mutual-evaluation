import Mathlib.Probability.Distributions.Uniform
import MutualEvaluation.Internal.CertificationDPI
import MutualEvaluation.Internal.CertificationCollision


noncomputable section
open Classical
open scoped BigOperators
namespace MutualEvaluation
local notation "mass" => (fun {A : Type} (p : PMF A) (a : A) => ENNReal.toReal (p a))
local notation "pair" => (fun {A B : Type} (p : PMF A) (q : PMF B) => PMF.bind p fun a => PMF.map (fun b => (a,b)) q)
namespace Certification.Proofs

theorem empirical_mass {A : Type} [Fintype A] {m : ℕ} [NeZero m]
    (z : Fin m → A) (a : A) :
    mass ((PMF.uniformOfFintype (Fin m)).map z) a =
      ∑ j : Fin m, (m : ℝ)⁻¹ * (if z j = a then 1 else 0) := by
  classical
  dsimp only
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp_all [eq_comm]
  · intro i _
    split_ifs <;> simp [PMF.uniformOfFintype_apply, NeZero.ne m]

theorem pure_pair {X Y : Type} (x : X) (y : Y) :
    pair (PMF.pure x) (PMF.pure y) = PMF.pure (x,y) := by
  simp [PMF.pure_map]

theorem empirical_pair {X Y : Type} {m : ℕ} [NeZero m]
    (z : Fin m → X × Y) :
    (PMF.uniformOfFintype (Fin m)).bind (fun i => pair (PMF.pure (z i).1) (PMF.pure (z i).2)) =
      (PMF.uniformOfFintype (Fin m)).map z := by
  simp only [pure_pair, Prod.mk.eta]
  rfl


theorem mass_sum {A : Type} [Fintype A] (p : PMF A) : ∑ a, mass p a = 1 := by
  have h := congrArg ENNReal.toReal p.tsum_coe
  rw [tsum_fintype, ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)] at h
  exact h

theorem mass_bind {A B : Type} [Fintype A] (p : PMF A) (k : A → PMF B) (b : B) :
    mass (p.bind k) b = ∑ a, mass p a * mass (k a) b := by
  simp only [PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top
    (p.apply_ne_top a) ((k a).apply_ne_top b))]
  simp only [ENNReal.toReal_mul]

theorem mass_pure {A : Type} (a b : A) : mass (PMF.pure a) b = if b = a then 1 else 0 := by
  by_cases h : b = a <;> simp [PMF.pure_apply, h]

theorem mass_pair {A B : Type} [Fintype A] [Fintype B]
    (p : PMF A) (q : PMF B) (a : A) (b : B) :
    mass (pair p q) (a,b) = mass p a * mass q b := by
  change mass (p.bind fun x => q.bind fun y => PMF.pure (x,y)) (a,b) = _
  simp only [mass_bind, mass_pure, Prod.mk.injEq]
  simp [ite_and]

theorem pair_map_fst {A B : Type} (p : PMF A) (q : PMF B) :
    (pair p q).map Prod.fst = p := by
  simp only [PMF.map_bind, PMF.map_comp]
  change (p.bind fun a => q.map (Function.const B a)) = p
  simp [PMF.map_const, PMF.bind_pure]

theorem pair_map_snd {A B : Type} (p : PMF A) (q : PMF B) :
    (pair p q).map Prod.snd = q := by
  simp only [PMF.map_bind, PMF.map_comp]
  change (p.bind fun _ => q.map id) = q
  simp [PMF.map_id]

theorem uniform_bind_mass {A : Type} {m : ℕ} [NeZero m] (k : Fin m → PMF A) (a : A) :
    mass ((PMF.uniformOfFintype (Fin m)).bind k) a = (∑ i, mass (k i) a) / m := by
  rw [mass_bind]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, Fintype.card_fin]
  rw [← Finset.mul_sum]
  ring

theorem uniform_latent_pmf_bound {X Y : Type} [Fintype X] [Fintype Y]
    {m : ℕ} [NeZero m] (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ici 0) f)
    (kx : Fin m → PMF X) (ky : Fin m → PMF Y) :
    let q := (PMF.uniformOfFintype (Fin m)).bind (fun i => pair (kx i) (ky i))
    divergence f (mass q) (fun xy => mass (q.map Prod.fst) xy.1 * mass (q.map Prod.snd) xy.2) ≤
      f m / m + (1 - 1/(m:ℝ))*f 0 := by
  dsimp only
  have h := uniform_latent_weights_bound f hf (fun i => mass (kx i)) (fun i => mass (ky i))
    (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ => ENNReal.toReal_nonneg)
    (fun i => mass_sum (kx i)) (fun i => mass_sum (ky i))
  have hx : ((PMF.uniformOfFintype (Fin m)).bind (fun i => pair (kx i) (ky i))).map Prod.fst =
      (PMF.uniformOfFintype (Fin m)).bind kx := by
    rw [PMF.map_bind]; simp only [pair_map_fst]
  have hy : ((PMF.uniformOfFintype (Fin m)).bind (fun i => pair (kx i) (ky i))).map Prod.snd =
      (PMF.uniformOfFintype (Fin m)).bind ky := by
    rw [PMF.map_bind]; simp only [pair_map_snd]
  rw [hx, hy]
  have hp : ∀ i (xy : X × Y), mass (pair (kx i) (ky i)) xy = mass (kx i) xy.1 * mass (ky i) xy.2 := by
    intro i xy; exact mass_pair _ _ _ _
  simpa only [uniform_bind_mass, hp] using h


theorem uniform_diagonal_pmf {m : ℕ} [NeZero m] (f : ℝ → ℝ) :
    let q := (PMF.uniformOfFintype (Fin m)).map (fun i => (i,i))
    divergence f (mass q) (fun xy => mass (q.map Prod.fst) xy.1 * mass (q.map Prod.snd) xy.2) =
      f m / m + (1 - 1/(m:ℝ))*f 0 := by
  dsimp only
  have hx : ((PMF.uniformOfFintype (Fin m)).map (fun i => (i,i))).map Prod.fst =
      PMF.uniformOfFintype (Fin m) := by
    rw [PMF.map_comp]; exact PMF.map_id _
  have hy : ((PMF.uniformOfFintype (Fin m)).map (fun i => (i,i))).map Prod.snd =
      PMF.uniformOfFintype (Fin m) := by
    rw [PMF.map_comp]; exact PMF.map_id _
  have hp : mass ((PMF.uniformOfFintype (Fin m)).map (fun i => (i,i))) =
      (fun ij : Fin m × Fin m => if ij.1 = ij.2 then (m:ℝ)⁻¹ else 0) := by
    funext ij
    rcases ij with ⟨a,b⟩
    rw [empirical_mass]
    simp [Prod.mk.injEq, ite_and, eq_comm]
  dsimp only at hp
  rw [hx, hy, hp]
  simpa only [PMF.uniformOfFintype_apply, Fintype.card_fin,
    ENNReal.toReal_inv, ENNReal.toReal_natCast] using uniform_diagonal_divergence (m:=m) f

theorem certification_pmf_bound {X Y : Type} [Fintype X] [Fintype Y]
    {m : ℕ} [NeZero m] (n : ℕ) (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ici 0) f)
    (L : (Fin n → X × Y) → ℝ) (δ : ℝ)
    (hvalid : ∀ q : PMF (X × Y), Collision.probability (mass q)
      (fun s => divergence f (mass q)
        (fun xy => mass (q.map Prod.fst) xy.1 * mass (q.map Prod.snd) xy.2) < L s) ≤ δ)
    (p : PMF (X × Y)) :
    Collision.probability (mass p) (fun s => f m/m + (1-1/(m:ℝ))*f 0 < L s) ≤
      δ + (Nat.choose n 2 : ℝ)/(m:ℝ) := by
  apply Collision.finite_confidence_transfer (mass p) (fun _ => ENNReal.toReal_nonneg)
    (mass_sum p) m n (Nat.pos_of_ne_zero (NeZero.ne m)) _ δ
  intro z
  let q := (PMF.uniformOfFintype (Fin m)).map z
  have hq := uniform_latent_pmf_bound f hf (fun i => PMF.pure (z i).1) (fun i => PMF.pure (z i).2)
  simp only [empirical_pair] at hq
  have hm : Collision.empirical (m:ℝ)⁻¹ z = mass q := by
    funext a
    exact (empirical_mass z a).symm
  rw [hm]
  apply le_trans (Collision.probability_mono (mass q) (fun _ => ENNReal.toReal_nonneg) _ _ _) (hvalid q)
  intro s hs
  exact lt_of_le_of_lt hq hs


/-- Exact diagonal evaluation oriented for the public semantic identity. -/
theorem uniformBound_semantic (f : ℝ → ℝ) (m : ℕ) [NeZero m] :
    f m / m + (1 - 1 / (m : ℝ)) * f 0 =
      let q := (PMF.uniformOfFintype (Fin m)).map (fun x => (x, x))
      ∑ xy, ((q.map Prod.fst) xy.1).toReal * ((q.map Prod.snd) xy.2).toReal *
        f ((q xy).toReal / (((q.map Prod.fst) xy.1).toReal * ((q.map Prod.snd) xy.2).toReal)) := by
  exact (uniform_diagonal_pmf (m := m) f).symm

/-- Combine the channel bound and the exact diagonal evaluation for the public statement. -/
theorem uniform_latent_dpi_statement {X Y : Type} [Fintype X] [Fintype Y]
    {m : ℕ} [NeZero m] (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ici 0) f)
    (kx : Fin m → PMF X) (ky : Fin m → PMF Y) :
    let q := (PMF.uniformOfFintype (Fin m)).bind (fun i => pair (kx i) (ky i))
    let diagonal := (PMF.uniformOfFintype (Fin m)).map (fun i => (i,i))
    let info := fun {A B : Type} [Fintype A] [Fintype B] (p : PMF (A × B)) =>
      divergence f (mass p) (fun xy => mass (p.map Prod.fst) xy.1 * mass (p.map Prod.snd) xy.2)
    info q ≤ info diagonal ∧ info diagonal = f m / m + (1 - 1/(m:ℝ))*f 0 := by
  dsimp only
  rw [uniform_diagonal_pmf]
  exact ⟨uniform_latent_pmf_bound f hf kx ky, rfl⟩

/-- Adapt finite-product sums to the public event-probability spelling.
No public definitions are redeclared here: this is only a proof-interface bridge. -/
theorem certification_statement {X Y : Type} [Fintype X] [Fintype Y]
    {m : ℕ} [NeZero m] (n : ℕ) (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ici 0) f)
    (L : (Fin n → X × Y) → ℝ) (δ : ℝ)
    (hvalid : ∀ q : PMF (X × Y),
      (∑ s : Fin n → X × Y, (∏ j, (q (s j)).toReal) *
        (if (∑ xy, ((q.map Prod.fst) xy.1).toReal * ((q.map Prod.snd) xy.2).toReal *
          f ((q xy).toReal / (((q.map Prod.fst) xy.1).toReal * ((q.map Prod.snd) xy.2).toReal)))
          < L s then 1 else 0)) ≤ δ)
    (p : PMF (X × Y)) :
    (∑ s : Fin n → X × Y, (∏ j, (p (s j)).toReal) *
      (if f m / m + (1 - 1/(m:ℝ))*f 0 < L s then 1 else 0)) ≤
      δ + (Nat.choose n 2 : ℝ)/(m:ℝ) := by
  have hv : ∀ q : PMF (X × Y), Collision.probability (mass q)
      (fun s => divergence f (mass q)
        (fun xy => mass (q.map Prod.fst) xy.1 * mass (q.map Prod.snd) xy.2) < L s) ≤ δ := by
    intro q
    have hh := hvalid q
    simp only [Collision.probability, Collision.weight, divergence] at hh ⊢
    convert hh using 1; congr!
  have hh := certification_pmf_bound (m := m) n f hf L δ hv p
  simp only [Collision.probability, Collision.weight] at hh ⊢
  convert hh using 1; congr!

end Certification.Proofs
end MutualEvaluation
