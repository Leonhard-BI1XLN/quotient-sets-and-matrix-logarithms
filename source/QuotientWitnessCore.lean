import Std

/-!
# A group-theoretic lemma and conditional uniformity of quotient-set witnesses

Run with Lean 4.36.0 and its standard library. No Mathlib dependency.

"conjugacy_gives_set_equality" proves a statement about every group and every
subset, finite or infinite, from elementary group axioms.

"uniform_witness" checks the model-theoretic deduction. First-order compactness,
availability of the indicated sentences, and the published classification of
balanced groups are its EXPLICIT PARAMETERS. This file does not certify the
classification, prove the first-order compactness theorem, or formalize the
syntax/semantics translation from the language of groups.
-/
namespace QuotientWitness
universe u v

/-- The group axioms used here, written explicitly to avoid dependencies. -/
structure GroupOps (X : Type u) where
  mul : X → X → X
  inv : X → X
  one : X
  assoc a b c : mul (mul a b) c = mul a (mul b c)
  one_mul a : mul one a = a
  mul_one a : mul a one = a
  inv_mul a : mul (inv a) a = one
  mul_inv a : mul a (inv a) = one

variable {X : Type u}

private theorem inv_of_product_one (G : GroupOps X) {a b : X} (h : G.mul a b = G.one) :
    G.inv a = b := calc
  G.inv a = G.mul (G.inv a) G.one := (G.mul_one _).symm
  _ = G.mul (G.inv a) (G.mul a b) := by rw [h]
  _ = G.mul (G.mul (G.inv a) a) b := (G.assoc ..).symm
  _ = b := by rw [G.inv_mul, G.one_mul]

private theorem inv_inv (G : GroupOps X) (a : X) : G.inv (G.inv a) = a :=
  inv_of_product_one G (G.inv_mul a)

private theorem inv_product (G : GroupOps X) (a b : X) :
    G.inv (G.mul a b) = G.mul (G.inv b) (G.inv a) := by
  apply inv_of_product_one
  rw [G.assoc, ← G.assoc b, G.mul_inv, G.one_mul, G.mul_inv]

/-- All conjugates of y belong to {y, y⁻¹}. -/
def Chi (G : GroupOps X) : Prop := ∀ x y,
  G.mul (G.mul x y) (G.inv x) = y ∨ G.mul (G.mul x y) (G.inv x) = G.inv y

/-- Predicates representing A⁻¹ A and A A⁻¹. -/
def leftQuot (G : GroupOps X) (A : X → Prop) (z : X) : Prop :=
  ∃ a b, A a ∧ A b ∧ z = G.mul (G.inv a) b
def rightQuot (G : GroupOps X) (A : X → Prop) (z : X) : Prop :=
  ∃ a b, A a ∧ A b ∧ z = G.mul a (G.inv b)

/-- Conjugate b a⁻¹ by a⁻¹ and conjugate a⁻¹ b by a. -/
theorem conjugacy_gives_set_equality (G : GroupOps X) (chi : Chi G) (A : X → Prop) :
    leftQuot G A = rightQuot G A := by
  funext z
  apply propext
  constructor
  · rintro ⟨a,b,ha,hb,rfl⟩
    have H := chi (G.inv a) (G.mul b (G.inv a))
    rw [inv_inv, G.assoc, G.assoc b, G.inv_mul, G.mul_one,
        inv_product, inv_inv] at H
    rcases H with e | e
    · exact ⟨b,a,hb,ha,e⟩
    · exact ⟨a,b,ha,hb,e⟩
  · rintro ⟨a,b,ha,hb,rfl⟩
    have H := chi b (G.mul (G.inv b) a)
    rw [← G.assoc b, G.mul_inv, G.one_mul, inv_product, inv_inv] at H
    rcases H with e | e
    · exact ⟨b,a,hb,ha,e⟩
    · exact ⟨a,b,ha,hb,e⟩

structure GroupModel where
  Carrier : Type u
  ops : GroupOps Carrier

/-- P is covered by at most t elements. The carrier of a group is nonempty. -/
def cardLE (P : X → Prop) (t : Nat) : Prop :=
  ∃ cover : Fin t → X, ∀ x, P x → ∃ i, cover i = x

/-- θ_n: for every tuple of k ≤ n entries, both quotient tables have equal
size. Each table has at most k² elements, so it is enough to compare the
finitely many thresholds t ≤ k². Repeated tuple entries are permitted. -/
def small (M : GroupModel) (n : Nat) : Prop :=
  ∀ k, k ≤ n → ∀ a : Fin k → M.Carrier, ∀ t, t ≤ k*k →
    let A := fun x => ∃ i, a i = x
    (cardLE (leftQuot M.ops A) t ↔ cardLE (rightQuot M.ops A) t)

theorem chi_implies_small (M : GroupModel) (chi : Chi M.ops) (n : Nat) : small M n := by
  intro k _ a t _
  dsimp only
  rw [conjugacy_gives_set_equality M.ops chi]

private theorem small_mono (M : GroupModel) {n k : Nat} (h : k ≤ n) (b : small M n) :
    small M k := by
  intro j hj
  exact b j (by omega)

/-- Compactness expressed for actual sentences of a language interpreted
in group models. The argument uses only this finite-satisfiability form. -/
def Compactness {Sentence : Type v} (sat : GroupModel.{u} → Sentence → Prop) : Prop :=
  ∀ theory : Sentence → Prop,
    (∀ fragment : List Sentence, (∀ s ∈ fragment, theory s) →
      ∃ M, ∀ s ∈ fragment, sat M s) →
    ∃ M, ∀ s, theory s → sat M s

private theorem bound_fragment {S : Type v} (neg : S) (theta : Nat → S) (fragment : List S)
    (inside : ∀ s ∈ fragment, s = neg ∨ ∃ k, s = theta k) :
    ∃ N, ∀ s ∈ fragment, s = neg ∨ ∃ k, k ≤ N ∧ s = theta k := by
  induction fragment with
  | nil => exact ⟨0,by simp⟩
  | cons a rest ih =>
    obtain ⟨N,tails⟩ := ih (fun s hs => inside s (by simp [hs]))
    obtain ha | ⟨k,ha⟩ := inside a (by simp)
    · refine ⟨N,?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | ht
      · exact Or.inl ha
      · exact tails s ht
    · refine ⟨max k N,?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | ht
      · exact Or.inr ⟨k,by omega,ha⟩
      · rcases tails s ht with hn | ⟨j,hj,he⟩
        · exact Or.inl hn
        · exact Or.inr ⟨j,by omega,he⟩

/-- The class indexed by "exceptional" in the application consists of the
seven finite exceptions in the published classification. "negSpec" and
"thetaSpec" explicitly link group-language sentences to mathematical predicates. -/
theorem uniform_witness {Sentence : Type v} (sat : GroupModel.{u} → Sentence → Prop)
    (compact : Compactness sat)
    (exceptional : GroupModel.{u} → Prop)
    (classification : ∀ M : GroupModel.{u},
      (∀ n, small M n) ↔ (Chi M.ops ∨ exceptional M))
    (neg : Sentence) (negSpec : ∀ M, sat M neg ↔ ¬ (Chi M.ops ∨ exceptional M))
    (theta : Nat → Sentence) (thetaSpec : ∀ M n, sat M (theta n) ↔ small M n) :
    ∃ N, ∀ M : GroupModel.{u}, ¬ (∀ n, small M n) → ¬ small M N := by
  classical
  apply Classical.byContradiction
  intro hNoBound
  let theory := fun s => s = neg ∨ ∃ n, s = theta n
  have finitelySat : ∀ fragment : List Sentence, (∀ s ∈ fragment, theory s) →
      ∃ M, ∀ s ∈ fragment, sat M s := by
    intro fragment inside
    obtain ⟨N,hN⟩ := bound_fragment neg theta fragment inside
    have existsBad : ∃ M : GroupModel.{u}, ¬ (∀ n, small M n) ∧ small M N := by
      apply Classical.byContradiction
      intro hn
      apply hNoBound
      refine ⟨N, ?_⟩
      intro M bad yes
      exact hn ⟨M,bad,yes⟩
    obtain ⟨M,bad,smallN⟩ := existsBad
    refine ⟨M,?_⟩
    intro s hs
    rcases hN s hs with rfl | ⟨j,hj,rfl⟩
    · exact (negSpec M).mpr (fun hc => bad ((classification M).mpr hc))
    · exact (thetaSpec M j).mpr (small_mono M hj smallN)
  obtain ⟨M,allSat⟩ := compact theory finitelySat
  have allSmall : ∀ n, small M n := fun n =>
    (thetaSpec M n).mp (allSat (theta n) (Or.inr ⟨n,rfl⟩))
  exact (negSpec M).mp (allSat neg (Or.inl rfl)) ((classification M).mp allSmall)

end QuotientWitness

#print axioms QuotientWitness.conjugacy_gives_set_equality
#print axioms QuotientWitness.uniform_witness
