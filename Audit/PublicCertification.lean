import MutualEvaluation.Public.Certification

#print axioms MutualEvaluation.Certification.fInformation
#print axioms MutualEvaluation.Certification.uniformBound
#print axioms MutualEvaluation.Certification.sampleProbability
#print axioms MutualEvaluation.Certification.uniformBound_semantic
#print axioms MutualEvaluation.Certification.distribution_free_certification

#print MutualEvaluation.Certification.uniformBound_semantic
#print MutualEvaluation.Certification.distribution_free_certification

-- A normalized convex generator outside the false uniform-support maximization claim.
example {X Y : Type} [Fintype X] [Fintype Y] {m : ℕ} [NeZero m]
    (n : ℕ) (L : (Fin n → X × Y) → ℝ) (δ : ℝ)
    (hvalid : ∀ q : PMF (X × Y), MutualEvaluation.Certification.sampleProbability q n
      (fun s => MutualEvaluation.Certification.fInformation (fun t => (t-1)^4) q < L s) ≤ δ)
    (p : PMF (X × Y)) :
    MutualEvaluation.Certification.sampleProbability p n
      (fun s => MutualEvaluation.Certification.uniformBound (fun t => (t-1)^4) m < L s) ≤
      δ + (Nat.choose n 2 : ℝ)/(m:ℝ) :=
  MutualEvaluation.Certification.distribution_free_certification n (fun t => (t-1)^4)
    MutualEvaluation.Certification.Proofs.quartic_convex
    L δ hvalid p

-- Semantic identity has no convexity or normalization assumptions.
example (f : ℝ → ℝ) (m : ℕ) [NeZero m] :
    MutualEvaluation.Certification.uniformBound f m =
      MutualEvaluation.Certification.fInformation f
        ((PMF.uniformOfFintype (Fin m)).map (fun x => (x, x))) :=
  MutualEvaluation.Certification.uniformBound_semantic f m

-- The certification interface accepts a convex generator with f 1 ≠ 0.
example {X Y : Type} [Fintype X] [Fintype Y] {m : ℕ} [NeZero m]
    (n : ℕ) (L : (Fin n → X × Y) → ℝ) (δ : ℝ)
    (hvalid : ∀ q : PMF (X × Y), MutualEvaluation.Certification.sampleProbability q n
      (fun s => MutualEvaluation.Certification.fInformation (fun _ => (7 : ℝ)) q < L s) ≤ δ)
    (p : PMF (X × Y)) :
    MutualEvaluation.Certification.sampleProbability p n
      (fun s => MutualEvaluation.Certification.uniformBound (fun _ => (7 : ℝ)) m < L s) ≤
      δ + (Nat.choose n 2 : ℝ) / (m : ℝ) :=
  MutualEvaluation.Certification.distribution_free_certification n (fun _ => (7 : ℝ))
    (convexOn_const _ (convex_Ici (0 : ℝ))) L δ hvalid p
