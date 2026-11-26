import Std

/-!
# The sharp six-element threshold in the infinite dihedral group

Lean 4.36 standard library. Rotations and reflections are indexed by all integers.
Finite subsets are represented by two lists of indices. Lists of total length
at most five give an explicit bijection of the two quotient sets; duplicate
listing is permitted. Conversely the displayed six distinct group elements
have exactly 13 right quotients and 14 left quotients.
-/
namespace DihedralSix

inductive D where
  | rot (x : Int)
  | refl (x : Int)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr
open D

def mul : D → D → D
  | rot x, rot y => rot (x + y)
  | rot x, refl y => refl (x + y)
  | refl x, rot y => refl (x - y)
  | refl x, refl y => rot (x - y)

def inv : D → D
  | rot x => rot (-x)
  | refl x => refl x

theorem group_laws :
    (∀ a b c, mul (mul a b) c = mul a (mul b c)) ∧
    (∀ a, mul (rot 0) a = a ∧ mul a (rot 0) = a ∧
      mul (inv a) a = rot 0 ∧ mul a (inv a) = rot 0) := by
  constructor
  · intro a b c
    cases a <;> cases b <;> cases c <;> simp [mul] <;> omega
  · intro a
    cases a <;> simp [mul, inv] <;> omega

def member (X Y : List Int) : D → Prop
  | rot x => x ∈ X
  | refl y => y ∈ Y

def rightQ (a b : D) : D := mul a (inv b)
def leftQ (a b : D) : D := mul (inv a) b

def quotients (op : D → D → D) (X Y : List Int) (z : D) : Prop :=
  ∃ a b, member X Y a ∧ member X Y b ∧ op a b = z

theorem rotations_match (X Y : List Int) (z : Int) :
    quotients rightQ X Y (rot z) ↔ quotients leftQ X Y (rot z) := by
  constructor <;> rintro ⟨a, b, ha, hb, e⟩ <;> cases a with
  | rot a =>
    cases b with
    | rot b =>
      exact ⟨rot b, rot a, hb, ha, by simp [rightQ, leftQ, mul, inv] at e ⊢; omega⟩
    | refl b => simp [rightQ, leftQ, mul, inv] at e
  | refl a =>
    cases b with
    | rot b => simp [rightQ, leftQ, mul, inv] at e
    | refl b => exact ⟨refl a, refl b, ha, hb, e⟩

theorem right_reflections (X Y : List Int) (z : Int) :
    quotients rightQ X Y (refl z) ↔ ∃ x ∈ X, ∃ y ∈ Y, z = x + y := by
  constructor
  · rintro ⟨a,b,ha,hb,e⟩
    cases a with
    | rot a =>
      cases b with
      | rot b => simp [rightQ,mul,inv] at e
      | refl b => exact ⟨a, ha, b, hb, by simpa [rightQ,mul,inv,eq_comm] using e⟩
    | refl a =>
      cases b with
      | rot b => exact ⟨b, hb, a, ha, by simp [rightQ,mul,inv] at e; omega⟩
      | refl b => simp [rightQ,mul,inv] at e
  · rintro ⟨x,hx,y,hy,rfl⟩
    exact ⟨rot x, refl y, hx, hy, rfl⟩

theorem left_reflections (X Y : List Int) (z : Int) :
    quotients leftQ X Y (refl z) ↔ ∃ x ∈ X, ∃ y ∈ Y, z = y - x := by
  constructor
  · rintro ⟨a,b,ha,hb,e⟩
    cases a with
    | rot a =>
      cases b with
      | rot b => simp [leftQ,mul,inv] at e
      | refl b => exact ⟨a, ha, b, hb, by simp [leftQ,mul,inv] at e; omega⟩
    | refl a =>
      cases b with
      | rot b => exact ⟨b, hb, a, ha, by simpa [leftQ,mul,inv,eq_comm] using e⟩
      | refl b => simp [leftQ,mul,inv] at e
  · rintro ⟨x,hx,y,hy,rfl⟩
    exact ⟨refl y, rot x, hy, hx, rfl⟩

/-- Every list of at most two integers is symmetric about a doubled center c. -/
theorem short_symmetric (X : List Int) (h : X.length ≤ 2) :
    ∃ c : Int, ∀ x, x ∈ X ↔ c - x ∈ X := by
  cases X with
  | nil => exact ⟨0, by simp⟩
  | cons a t =>
    cases t with
    | nil => exact ⟨2*a, by intro x; simp; omega⟩
    | cons b t =>
      cases t with
      | nil =>
        refine ⟨a+b, ?_⟩
        intro x
        simp
        omega
      | cons c t => simp at h

/-- This predicate supplies explicit mutually inverse maps on all of D
    which restrict to a bijection of the two quotient sets. -/
def balanced (X Y : List Int) : Prop :=
  ∃ f g : D → D, (∀ a, g (f a) = a) ∧ (∀ a, f (g a) = a) ∧
    ∀ a, quotients rightQ X Y a ↔ quotients leftQ X Y (f a)

def onReflections (f : Int → Int) : D → D
  | rot z => rot z
  | refl z => refl (f z)

theorem all_at_most_five_balance (X Y : List Int) (h : X.length + Y.length ≤ 5) :
    balanced X Y := by
  by_cases hx : X.length ≤ 2
  · obtain ⟨c, hsym⟩ := short_symmetric X hx
    refine ⟨onReflections (fun z => z - c), onReflections (fun z => z + c), ?_, ?_, ?_⟩
    · intro a; cases a <;> simp [onReflections] <;> omega
    · intro a; cases a <;> simp [onReflections] <;> omega
    · intro a
      cases a with
      | rot z => exact rotations_match X Y z
      | refl z =>
        rw [right_reflections]
        change _ ↔ quotients leftQ X Y (refl (z-c))
        rw [left_reflections]
        constructor <;> rintro ⟨x,hx',y,hy',eq⟩ <;>
          exact ⟨c-x, (hsym x).mp hx', y, hy', by omega⟩
  · have hy : Y.length ≤ 2 := by omega
    obtain ⟨c, hsym⟩ := short_symmetric Y hy
    refine ⟨onReflections (fun z => c - z), onReflections (fun z => c - z), ?_, ?_, ?_⟩
    · intro a; cases a <;> simp [onReflections] <;> omega
    · intro a; cases a <;> simp [onReflections] <;> omega
    · intro a
      cases a with
      | rot z => exact rotations_match X Y z
      | refl z =>
        rw [right_reflections]
        change _ ↔ quotients leftQ X Y (refl (c-z))
        rw [left_reflections]
        constructor <;> rintro ⟨x,hx',y,hy',eq⟩ <;>
          exact ⟨x, hx', c-y, (hsym y).mp hy', by omega⟩

def six : List D := [rot 0, rot 1, rot 3, refl 0, refl 1, refl 3]

def rotations : List D → List Int
  | [] => []
  | rot x :: t => x :: rotations t
  | refl _ :: t => rotations t

def reflections : List D → List Int
  | [] => []
  | rot _ :: t => reflections t
  | refl x :: t => x :: reflections t

theorem split_length (A : List D) : (rotations A).length + (reflections A).length = A.length := by
  induction A with
  | nil => rfl
  | cons a t ih => cases a <;> simp [rotations, reflections] <;> omega

theorem split_membership (A : List D) (z : D) : member (rotations A) (reflections A) z ↔ z ∈ A := by
  induction A with
  | nil => cases z <;> simp [rotations, reflections, member]
  | cons a t ih =>
    cases a <;> cases z <;> simp [rotations, reflections, member] at ih ⊢ <;> simp [ih]

def distinct : List D → List D
  | [] => []
  | a :: t => if a ∈ distinct t then distinct t else a :: distinct t

theorem mem_distinct (A : List D) (x : D) : x ∈ distinct A ↔ x ∈ A := by
  induction A with
  | nil => simp [distinct]
  | cons a t ih =>
    rw [distinct]
    split
    · rename_i h
      simp only [List.mem_cons]
      constructor
      · exact fun hx => Or.inr (ih.mp hx)
      · rintro (rfl | hx)
        · exact h
        · exact ih.mpr hx
    · simp [ih]

theorem distinct_nodup (A : List D) : (distinct A).Nodup := by
  induction A with
  | nil => simp [distinct]
  | cons a t ih =>
    rw [distinct]
    split
    · exact ih
    · rename_i h
      exact List.nodup_cons.mpr ⟨h,ih⟩

def enumerate (op : D → D → D) (A : List D) : List D :=
  distinct (A.flatMap (fun a => A.map (op a)))

theorem enumerate_iff (op : D → D → D) (A : List D) (z : D) :
    z ∈ enumerate op A ↔ quotients op (rotations A) (reflections A) z := by
  simp only [enumerate, mem_distinct, List.mem_flatMap, List.mem_map, quotients, split_membership]
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    exact ⟨a, b, ha, hb, h⟩
  · rintro ⟨a, b, ha, hb, h⟩
    exact ⟨a, ha, b, hb, h⟩

/-- The ordinary numerical cardinalities are equal for any listing of at most
    five elements of the infinite group. No enumeration of group elements is used. -/
theorem five_equal_cardinalities (A : List D) (h : A.length ≤ 5) :
    (enumerate rightQ A).length = (enumerate leftQ A).length := by
  obtain ⟨f,g,hgf,hfg,hm⟩ := all_at_most_five_balance _ _ ((split_length A) ▸ h)
  have hmap (z : D) : z ∈ enumerate rightQ A ↔ f z ∈ enumerate leftQ A := by
    simpa only [enumerate_iff] using hm z
  have finj (a b : D) (hab : f a = f b) : a = b := by
    rw [← hgf a, ← hgf b, hab]
  have hR : (enumerate rightQ A).Nodup := distinct_nodup _
  have hL : (enumerate leftQ A).Nodup := distinct_nodup _
  have hFR : ((enumerate rightQ A).map f).Nodup :=
    hR.map f (fun a b hne eq => hne (finj a b eq))
  have hperm := (List.perm_ext_iff_of_nodup hFR hL).mpr (by
    intro z
    rw [List.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hmap a).mp ha
    · intro hz
      exact ⟨g z, (hmap (g z)).mpr (by rwa [hfg]), hfg z⟩)
  simpa using hperm.length_eq


private theorem dedup_input_invariant (op : D → D → D) (A : List D) :
    (enumerate op A).length = (enumerate op (distinct A)).length := by
  have h1 : (enumerate op A).Nodup := distinct_nodup _
  have h2 : (enumerate op (distinct A)).Nodup := distinct_nodup _
  apply List.Perm.length_eq
  apply (List.perm_ext_iff_of_nodup h1 h2).mpr
  intro z
  simp only [enumerate, mem_distinct, List.mem_flatMap, List.mem_map]

/-- Stated in terms of the number of distinct input elements, regardless of
    how often they occur in the finite presentation A. -/
theorem five_distinct_equal_cardinalities (A : List D) (h : (distinct A).length ≤ 5) :
    (enumerate rightQ A).length = (enumerate leftQ A).length := by
  rw [dedup_input_invariant rightQ A, dedup_input_invariant leftQ A]
  exact five_equal_cardinalities (distinct A) h

theorem six_is_sharp :
    six.Nodup ∧ six.length = 6 ∧ (enumerate rightQ six).length = 13 ∧
    (enumerate leftQ six).length = 14 := by decide

theorem inverse_six_positive :
    (enumerate rightQ (six.map inv)).length = 14 ∧
    (enumerate leftQ (six.map inv)).length = 13 := by decide

end DihedralSix

#print axioms DihedralSix.five_distinct_equal_cardinalities
#print axioms DihedralSix.six_is_sharp
