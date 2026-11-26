import Std

/-!
# Ingredients in the growth of quotient-set differences

This standalone file uses Lean 4.36 and its standard library.

* A gap with the exact signed counting formula of the non-FC construction
  grows in absolute value beyond every bound.
* On a homogeneous infinite subsequence, two word templates cannot be equal
  if one contains an index exactly once (injectively) and the other omits it.
* Repeated doubling or tripling of a positive gap gives unbounded gaps.
* In every group, translating a set A by an element t centralizing A and
  adjoining this translate changes each original quotient Q to Q ∪ tQ ∪ t⁻¹Q.

The infinite Ramsey theorem, the group constructions producing the templates
and counts, and the FC-group choice of disjoint translates are outside this file.
-/

namespace QuotientGrowth
universe u v

/-- The factorization is twice the signed difference
  a (n-1) + d binom(n,2), where a is positive and d is any integer. -/
theorem counting_formula_forces_growth (a : Nat) (ha : 0 < a) (d : Int)
    (gap : Nat → Int)
    (formula : ∀ n : Nat, 1 ≤ n →
      2 * gap n = ((n : Int) - 1) * (2 * (a : Int) + d * (n : Int))) :
    ∀ bound : Nat, ∃ cutoff : Nat, ∀ n ≥ cutoff,
      (bound : Int) ≤ gap n ∨ (bound : Int) ≤ -(gap n) := by
  intro bound
  refine ⟨2 * bound + 2 * a + 3, ?_⟩
  intro n hn
  have hn0 : 0 ≤ (n : Int) := by omega
  have hn1 : 0 ≤ (n : Int) - 1 := by omega
  have hgap := formula n (by omega)
  by_cases hd : 0 ≤ d
  · left
    have hdn := Int.mul_nonneg hd hn0
    have hfactor : 1 ≤ 2 * (a : Int) + d * (n : Int) := by omega
    have h := Int.mul_le_mul_of_nonneg_left hfactor hn1
    rw [Int.mul_one] at h
    omega
  · right
    have hd' : d ≤ -1 := by omega
    have hdn := Int.mul_le_mul_of_nonneg_right hd' hn0
    simp only [Int.neg_one_mul] at hdn
    have hfactor : 2 * (a : Int) + d * (n : Int) ≤ -1 := by omega
    have h := Int.mul_le_mul_of_nonneg_left hfactor hn1
    rw [Int.mul_neg_one] at h
    omega

/-- Coordinates are indices in the ordered infinite subsequence. -/
def Increasing {k : Nat} (indices : Fin k → Nat) : Prop :=
  ∀ i j, i.val < j.val → indices i < indices j

def AgreeOff {k : Nat} (v : Fin k) (p q : Fin k → Nat) : Prop :=
  ∀ i, i ≠ v → p i = q i

/-- Two increasing index tuples which differ precisely in any prescribed
    coordinate. This is why single indices can be varied on a homogeneous
    infinite subsequence, including the first and last coordinate. -/
theorem separated_tuples {k : Nat} (v : Fin k) :
    ∃ p q : Fin k → Nat, Increasing p ∧ Increasing q ∧ AgreeOff v p q ∧ p v ≠ q v := by
  let p : Fin k → Nat := fun i => 2 * i.val
  let q : Fin k → Nat := fun i => 2 * i.val + (if i = v then 1 else 0)
  refine ⟨p, q, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    dsimp [p]
    omega
  · intro i j hij
    dsimp [q]
    split <;> split <;> omega
  · intro i hiv
    simp [p, q, hiv]
  · simp [p, q]

/-- An equality between templates cannot hold on every increasing tuple if
    one side is injective in a coordinate which the other side ignores. -/
theorem no_homogeneous_single_index_equality {α : Type v} {k : Nat} (v : Fin k)
    (f h : (Fin k → Nat) → α)
    (injectiveAt : ∀ p q, AgreeOff v p q → f p = f q → p v = q v)
    (absentAt : ∀ p q, AgreeOff v p q → h p = h q) :
    ¬ ∀ p, Increasing p → f p = h p := by
  intro homogeneous
  obtain ⟨p, q, hp, hq, hagree, hne⟩ := separated_tuples v
  apply hne
  apply injectiveAt p q hagree
  calc
    f p = h p := homogeneous p hp
    _ = h q := absentAt p q hagree
    _ = f q := (homogeneous q hq).symm

/-- The abstract amplification step used by the FC case. A value belongs
    to att if it occurs as the positive difference of a finite witness. -/
theorem unbounded_of_doubling_or_tripling (att : Int → Prop)
    (seed : ∃ x, att x ∧ 0 < x)
    (step : ∀ x, att x → 0 < x → att (2 * x) ∨ att (3 * x)) :
    ∀ b : Nat, ∃ x : Int, att x ∧ (b : Int) < x := by
  intro b
  induction b with
  | zero => simpa using seed
  | succ b ih =>
    obtain ⟨x, hx, hbx⟩ := ih
    have hpos : 0 < x := by omega
    rcases step x hx hpos with h2 | h3
    · exact ⟨2 * x, h2, by omega⟩
    · exact ⟨3 * x, h3, by omega⟩

/-- Only multiplication, inverses, and the ordinary group axioms are used
    in the verification of single-occurrence word cancellation. -/
structure GroupOps (X : Type u) where
  mul : X → X → X
  inv : X → X
  one : X
  assoc a b c : mul (mul a b) c = mul a (mul b c)
  one_mul a : mul one a = a
  mul_one a : mul a one = a
  inv_mul a : mul (inv a) a = one
  mul_inv a : mul a (inv a) = one

namespace GroupOps

variable {X : Type u} (G : GroupOps X)

private theorem cancel_left (a x y : X) (h : G.mul a x = G.mul a y) : x = y := by
  have h' := congrArg (G.mul (G.inv a)) h
  simpa only [← G.assoc, G.inv_mul, G.one_mul] using h'

private theorem cancel_right (a x y : X) (h : G.mul x a = G.mul y a) : x = y := by
  have h' := congrArg (fun z => G.mul z (G.inv a)) h
  simpa only [G.assoc, G.mul_inv, G.mul_one] using h'

private theorem inverse_injective (x y : X) (h : G.inv x = G.inv y) : x = y := by
  apply G.cancel_left (G.inv x)
  calc
    G.mul (G.inv x) x = G.one := G.inv_mul x
    _ = G.mul (G.inv x) y := by rw [h, G.inv_mul]

/-- Every group word in which an index occurs exactly once takes this
    form after fixing the other coordinates and reassociating. -/
def singleWord (a b x : X) (inverse : Bool) : X :=
  G.mul (G.mul a (if inverse then G.inv x else x)) b

theorem singleWord_injective (a b : X) (inverse : Bool) {x y : X}
    (e : G.singleWord a b x inverse = G.singleWord a b y inverse) : x = y := by
  have h := G.cancel_left a _ _ (G.cancel_right b _ _ e)
  cases inverse with
  | false => exact h
  | true => exact G.inverse_injective x y h

/-- A concrete group-word version of the homogeneous-coloring lemma. The
    coefficients on either side of the selected index may depend on every
    other index. The infinite sequence of group elements need only be injective. -/
theorem no_homogeneous_group_equality {k : Nat} (v : Fin k)
    (sequence : Nat → X) (hinj : ∀ i j, sequence i = sequence j → i = j)
    (left right omitted : (Fin k → Nat) → X) (inverse : Bool)
    (unchanged : ∀ p q, AgreeOff v p q →
      left p = left q ∧ right p = right q ∧ omitted p = omitted q) :
    ¬ ∀ p, Increasing p →
      G.singleWord (left p) (right p) (sequence (p v)) inverse = omitted p := by
  apply no_homogeneous_single_index_equality v
    (fun p => G.singleWord (left p) (right p) (sequence (p v)) inverse) omitted
  · intro p q agree equality
    obtain ⟨hl, hr, _⟩ := unchanged p q agree
    rw [hl, hr] at equality
    exact hinj _ _ (G.singleWord_injective _ _ _ equality)
  · intro p q agree
    exact (unchanged p q agree).2.2

private theorem inverse_product (x y : X) :
    G.inv (G.mul x y) = G.mul (G.inv y) (G.inv x) := by
  apply G.cancel_left (G.mul x y)
  rw [G.mul_inv, G.assoc, ← G.assoc y, G.mul_inv, G.one_mul, G.mul_inv]

private theorem commute_inv {x y : X} (h : G.mul x y = G.mul y x) :
    G.mul x (G.inv y) = G.mul (G.inv y) x := by
  apply G.cancel_right y
  rw [G.assoc, G.inv_mul, G.mul_one, G.assoc, h, ← G.assoc, G.inv_mul, G.one_mul]

private theorem commute_product {t x y : X}
    (hx : G.mul t x = G.mul x t) (hy : G.mul t y = G.mul y t) :
    G.mul t (G.mul x y) = G.mul (G.mul x y) t := by
  rw [← G.assoc, hx, G.assoc, hy, G.assoc]

def translated (t : X) (i : Bool) (a : X) : X := if i then G.mul t a else a

/-- Sign of the translate in the right quotient, for the two choices of copy. -/
def translateQuot (t : X) (i j : Bool) (z : X) : X :=
  match i, j with
  | true, false => G.mul t z
  | false, true => G.mul (G.inv t) z
  | _, _ => z

/-- Elementwise form of the three translated copies of AA⁻¹.
    Only the two elements involved must commute with the translating element. -/
theorem right_of_translates (t a b : X) (i j : Bool)
    (ha : G.mul t a = G.mul a t) (hb : G.mul t b = G.mul b t) :
    G.mul (G.translated t i a) (G.inv (G.translated t j b)) =
      G.translateQuot t i j (G.mul a (G.inv b)) := by
  have hq := G.commute_product ha (G.commute_inv hb)
  have hiq := G.commute_inv hq.symm
  cases i <;> cases j
  · rfl
  · simp only [translated, Bool.false_eq_true, ↓reduceIte, translateQuot, inverse_product]
    rw [← G.assoc]
    exact hiq
  · exact G.assoc .. 
  · simp only [translated, ↓reduceIte, translateQuot, inverse_product]
    calc
      G.mul (G.mul t a) (G.mul (G.inv b) (G.inv t)) =
        G.mul (G.mul t (G.mul a (G.inv b))) (G.inv t) := by simp only [G.assoc]
      _ = G.mul a (G.inv b) := by rw [hq, G.assoc, G.mul_inv, G.mul_one]

/-- Elementwise form of the three translated copies of A⁻¹A. The two copy
    indices are reversed in comparison with the right quotient. -/
theorem left_of_translates (t a b : X) (i j : Bool)
    (ha : G.mul t a = G.mul a t) :
    G.mul (G.inv (G.translated t i a)) (G.translated t j b) =
      G.translateQuot t j i (G.mul (G.inv a) b) := by
  have hta := G.commute_inv ha
  have hai := G.commute_inv hta.symm
  cases i <;> cases j
  · rfl
  · simp only [translated, Bool.false_eq_true, ↓reduceIte, translateQuot]
    rw [← G.assoc, ← hta, G.assoc]
  · simp only [translated, Bool.false_eq_true, ↓reduceIte, translateQuot, inverse_product]
    rw [hai, G.assoc]
  · simp only [translated, ↓reduceIte, translateQuot, inverse_product]
    rw [G.assoc, ← G.assoc (G.inv t), G.inv_mul, G.one_mul]

def unionOfCopies (t : X) (A : X → Prop) (x : X) : Prop :=
  ∃ (i : Bool) (a : X), A a ∧ G.translated t i a = x

def pairImage (op : X → X → X) (A : X → Prop) (x : X) : Prop :=
  ∃ a b, A a ∧ A b ∧ op a b = x

def threeCopies (t : X) (Q : X → Prop) (x : X) : Prop :=
  Q x ∨ ∃ y, Q y ∧ (G.mul t y = x ∨ G.mul (G.inv t) y = x)

private theorem image_of_copies (t : X) (A : X → Prop) (op : X → X → X)
    (shift : Bool → Bool → X → X)
    (factor : ∀ i j a b, A a → A b →
       op (G.translated t i a) (G.translated t j b) = shift i j (op a b))
    (x : X) :
    pairImage op (G.unionOfCopies t A) x ↔
      ∃ i j y, pairImage op A y ∧ shift i j y = x := by
  constructor
  · rintro ⟨ac, bc, ⟨i, a, ha, rfl⟩, ⟨j, b, hb, rfl⟩, h⟩
    exact ⟨i, j, op a b, ⟨a, b, ha, hb, rfl⟩, (factor i j a b ha hb).symm.trans h⟩
  · rintro ⟨i, j, y, ⟨a, b, ha, hb, rfl⟩, h⟩
    exact ⟨_, _, ⟨i, a, ha, rfl⟩, ⟨j, b, hb, rfl⟩, (factor i j a b ha hb).trans h⟩

private theorem all_shifts (t : X) (Q : X → Prop) (x : X) :
    (∃ i j y, Q y ∧ G.translateQuot t i j y = x) ↔ G.threeCopies t Q x := by
  constructor
  · rintro ⟨i, j, y, hy, h⟩
    cases i <;> cases j
    · exact Or.inl (h ▸ hy)
    · exact Or.inr ⟨y, hy, Or.inr h⟩
    · exact Or.inr ⟨y, hy, Or.inl h⟩
    · exact Or.inl (h ▸ hy)
  · rintro (hx | ⟨y, hy, h | h⟩)
    · exact ⟨false, false, x, hx, rfl⟩
    · exact ⟨true, false, y, hy, h⟩
    · exact ⟨false, true, y, hy, h⟩

/-- Exact set identity for the right quotient of B = A ∪ tA:
    BB⁻¹ is R ∪ tR ∪ t⁻¹R where R = AA⁻¹. -/
theorem right_union_identity (t : X) (A : X → Prop)
    (centralizes : ∀ a, A a → G.mul t a = G.mul a t) (x : X) :
    pairImage (fun a b => G.mul a (G.inv b)) (G.unionOfCopies t A) x ↔
    G.threeCopies t (pairImage (fun a b => G.mul a (G.inv b)) A) x := by
  exact (G.image_of_copies t A _ (G.translateQuot t)
    (fun i j a b ha hb => G.right_of_translates t a b i j
      (centralizes a ha) (centralizes b hb)) x).trans (G.all_shifts t _ x)

/-- Exact set identity for the left quotient of B = A ∪ tA:
    B⁻¹B is L ∪ tL ∪ t⁻¹L where L = A⁻¹A. -/
theorem left_union_identity (t : X) (A : X → Prop)
    (centralizes : ∀ a, A a → G.mul t a = G.mul a t) (x : X) :
    pairImage (fun a b => G.mul (G.inv a) b) (G.unionOfCopies t A) x ↔
    G.threeCopies t (pairImage (fun a b => G.mul (G.inv a) b) A) x := by
  refine (G.image_of_copies t A _ (fun i j => G.translateQuot t j i)
    (fun i j a b ha _ => G.left_of_translates t a b i j (centralizes a ha)) x).trans ?_
  refine Iff.trans ?_ (G.all_shifts t _ x)
  constructor <;> rintro ⟨i, j, y, hy, h⟩ <;> exact ⟨j, i, y, hy, h⟩

end GroupOps

end QuotientGrowth

#print axioms QuotientGrowth.counting_formula_forces_growth
#print axioms QuotientGrowth.GroupOps.no_homogeneous_group_equality
#print axioms QuotientGrowth.GroupOps.right_union_identity
#print axioms QuotientGrowth.GroupOps.left_union_identity
