import MutualEvaluation.Internal.Certification

/-!
# Uniform-latent certification bound
-/
noncomputable section
open scoped BigOperators
open Classical
namespace MutualEvaluation.Certification

/-- The finite-alphabet f-information functional, comparing the joint law `q`
with the product of its marginals.
When `f` is convex on the nonnegative reals and `f 1 = 0`, this is the
f-mutual information.
The definition itself imposes no assumptions on `f`. -/
def fInformation {X Y : Type} [Fintype X] [Fintype Y]
    (f : ℝ → ℝ) (q : PMF (X × Y)) : ℝ :=
  ∑ xy, ((q.map Prod.fst) xy.1).toReal * ((q.map Prod.snd) xy.2).toReal *
    f ((q xy).toReal / (((q.map Prod.fst) xy.1).toReal * ((q.map Prod.snd) xy.2).toReal))

/-- For positive m, information when X=Y is uniformly distributed over m letters. -/
def uniformBound (f : ℝ → ℝ) (m : ℕ) : ℝ :=
  f m / m + (1 - 1 / (m : ℝ)) * f 0

/-- The uniform bound equals the f-information of a uniform diagonal law. -/
theorem uniformBound_semantic (f : ℝ → ℝ)
    (m : ℕ) [NeZero m] :
    uniformBound f m =
      fInformation f
        ((PMF.uniformOfFintype (Fin m)).map
          (fun x => (x, x))) :=
  Proofs.uniformBound_semantic f m

/-- A sample probability returns a real number.
The (finite) type A denotes individual sample outcomes where q is the PMF over A.
The term n indicates the number of independent samples. E is the event; a predicate over sequences of these samples.
The value is calculated by summing over each possible sample sequence s satisfying E, weighted by its probability. -/
def sampleProbability {A : Type} [Fintype A] (q : PMF A) (n : ℕ)
    (E : (Fin n → A) → Prop) : ℝ :=
  ∑ s, (∏ i, (q (s i)).toReal) * (if E s then 1 else 0)

/-- Distribution-free certification cannot exceed the uniform bound except at confidence
error plus a collision-probability bound.
Let L map a sample sequence s to a real value L s.
Assume that, for every PMF q over X × Y, the probability that L s exceeds
the f-information of q on n independent samples is at most δ.
Then, for every PMF p over X × Y, the probability that L s exceeds the
uniform bound over m letters is at most δ + (n choose 2) / m.
The second term bounds the probability of a repeated latent index among
n independent uniform draws from m letters.

Only convexity of f on the nonnegative reals is required;
no normalization such as f 1 = 0 is needed. -/
theorem distribution_free_certification {X Y : Type} [Fintype X] [Fintype Y]
    {m : ℕ} [NeZero m] (n : ℕ) (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ici 0) f)
    (L : (Fin n → X × Y) → ℝ) (δ : ℝ)
    (hvalid : ∀ q : PMF (X × Y),
      sampleProbability q n (fun s => fInformation f q < L s) ≤ δ)
    (p : PMF (X × Y)) :
    sampleProbability p n (fun s => uniformBound f m < L s) ≤
      δ + (Nat.choose n 2 : ℝ) / (m : ℝ) :=
  Proofs.certification_statement n f hf L δ hvalid p

end MutualEvaluation.Certification
